local_server = "http://127.0.0.1:5000"
cy = null;

currentNodeId = null;
currentNode = null

selectedEdge = null;

let addedNodes = [];
let addedEdges = [];
let specDefs = [];

// Stores source node from which to create support lemma edge.
let supportLemmaTarget = null;

let awaitPollIntervalMS = 2000;

cytoscape.warnings(false);


function awaitGenCtiCompletion(expr){
    $.get(local_server + `/getActiveCtiGenThreads`, function(data){
        console.log("checking active cti threads:", data)

        let active_threads = data["active_threads"];
        $('#gen-ctis-btn').prop("disabled",true);
        $('#gen-ctis-btn-subtree').prop("disabled",true);
        if(active_threads.length > 0){
            setTimeout(() => awaitGenCtiCompletion(expr), awaitPollIntervalMS);
        } else{
            // Once active CTI gen thread completes, refresh the proof graph.
            reloadProofGraph();
            $('#gen-ctis-btn').prop("disabled",false);
            $('#gen-ctis-btn-subtree').prop("disabled",false);
            $('#cti-loading-icon').hide();
        }
    });
}

function genCtis(exprName){
    console.log("Generating CTIs for '" + exprName + "'");
    $('#cti-loading-icon').css('visibility', 'visible');

    $.get(local_server + `/genCtis/single/${exprName}`, function(data){
        console.log(data);
        awaitGenCtiCompletion(exprName);
    });
}

function genCtisSubtree(exprName){
    console.log("Gen CTIs recursive", exprName);
    $.get(local_server + `/genCtis/subtree/${exprName}`, function(data){
        console.log(data);
        awaitGenCtiCompletion(exprName);
    });
}

function addLemmaNode(lemmaName){
    console.log("Adding lemma:", lemmaName);
    $.get(local_server + `/addNode/${lemmaName}`, function(data){
        reloadProofGraph();
    });
}

function deleteSupportLemmaEdge(edge){

    let source = edge.data()["source"];
    let sourceNode = edge.data()["child"];
    let target = edge.data()["targetNode"];
    let action = edge.data()["action"];
    let parentId = edge.data()["targetParentId"];

    console.log("Deleting support edge, target:", target, ", source:", source, ", action: ", action);
    $.get(local_server + `/deleteSupportEdge/${target["name"]}/${action}/${sourceNode["name"]}`, function(data){
        console.log(data);
        console.log("add edge complete.");

        // Once we added the new support edge, we should reload the proof graph and re-generate CTIs
        // for the target node.
        reloadProofGraph();
        genCtis(target["name"]);
    });
}

function addSupportLemmaEdge(target, action, src){
    console.log("Adding support edge, target:", target, ", source:", src, ", action: ", action);
    $.get(local_server + `/addSupportEdge/${target}/${action}/${src}`, function(data){
        console.log(data);
        console.log("add edge complete.");

        // Once we added the new support edge, we should reload the proof graph and re-generate CTIs
        // for the target node.
        reloadProofGraph(function(){
            genCtis(target);
        });
    });
}

function setCTIPaneHtml(nodeData){
    var ctipane = document.getElementById("ctiPane");
    ctipane.innerHTML = "<h1> CTI View </h1>";
    let nodeIdText = currentNodeId;
    if(nodeData && nodeData["actionNode"]){
        nodeIdText = nodeData["parentId"] + " -> " + currentNodeId + "";
    }

    ctipane.innerHTML += '<div id="cti-loading-icon">Generating CTIs <i class="fa fa-refresh fa-spin"></i></div>';
    ctipane.innerHTML += `<h3> Proof node: ${nodeIdText} </h3>`;

    // For now don't allow CTI generation for specific sub-actions, only for top-level node all at once.
    if(nodeData && !nodeData["actionNode"]){
        ctipane.innerHTML += "<div><button id='gen-ctis-btn'> Gen CTIs </button></div> <br>";
        ctipane.innerHTML += "<div><button id='gen-ctis-btn-subtree'> Gen CTIs (recursive) </button></div> <br>";
    }

    ctipane.innerHTML += "<div><button id='refresh-node-btn'> Refresh Proof Node </button></div> <br>";
    ctipane.innerHTML += "<div><button id='add-support-lemma-btn'> Add support lemma </button></div><br>";
    ctipane.innerHTML += "<div><button id='delete-support-edge-btn'> Delete selected support lemma </button></div>";

    ctipane.innerHTML += '<label for="lemmas">Choose a lemma node to add:</label>';
    let selectHTML = '<select name="lemmas" id="lemma-selection">';
    for(const def of specDefs){
        if(def.startsWith("H_")){
            selectHTML += `<option value="${def}">${def}</option>`;
        }
    }
    selectHTML += '</select>';
    ctipane.innerHTML += selectHTML;
    ctipane.innerHTML += "<div><button id='add-lemma-node-btn'> Add lemma </button></div>";


    $('#cti-loading-icon').css('visibility', 'hidden');
    $('#delete-support-edge-btn').css('visibility', 'hidden');

    $('#delete-support-edge-btn').on('click', function(ev){
        console.log("CLICKED delete button.");
        if(selectedEdge === null){
            return;
        }
        console.log("deleting edge");
        deleteSupportLemmaEdge(selectedEdge);
    })

    $('#add-lemma-node-btn').on('click', function(ev){
        let selectedLemma = $("#lemma-selection").find(":selected").val();
        addLemmaNode(selectedLemma);
    })
}

function computeNodeColor(data, action){
    if(action === undefined){
        // If node is not an action node then compute based on all CTIs for
        // this node.
        ctis = [];
        ctis_eliminated = [];
        for(const action in data["ctis"]){
            ctis = ctis.concat(data["ctis"][action]);
            ctis_eliminated = ctis_eliminated.concat(data["ctis_eliminated"][action]);
        }
        console.log(data["name"]);
        console.log(data["ctis"]);
    } else{
        ctis = data["ctis"][action];
        ctis_eliminated = data["ctis_eliminated"][action];
    }
    console.log(data);

    if(data["had_ctis_generated"] && ctis.length === ctis_eliminated.length){
        // style = {"background-color": "green"}
        return "green";
    }
    if(!data["had_ctis_generated"]){
        if(action !== undefined){
            return "lightgray";
        }
        return "gray";
    }
    return "orange";
}


function refreshNode(nodeId){
    console.log("Refreshing proof node '" + nodeId + "'");
    focusOnNode(nodeId);
    $.get(local_server + `/getNode/${nodeId}`, function(data){
        console.log(data);

        let color = computeNodeColor(data);
        cy.nodes(`node[name = "${nodeId}"]`).style('background-color', color);

    });   
}

function focusOnNode(nodeId, nodeData){
    if(currentNodeId === nodeId){
        return;
    }
    console.log("Focus on node: ", nodeId);
    currentNodeId = nodeId;
    console.log(nodeData);
    setCTIPaneHtml(nodeData);

    let nodeIdArg = nodeId;
    // For action nodes, we want to get the data for the associated parent node.
    if(nodeData["actionNode"]){
        nodeIdArg = nodeData["parentId"];
    }

    $.get(local_server + `/getNode/${nodeIdArg}`, function(data){
        console.log("Retrieved CTIs for '" + nodeId + "'");
        console.log("node data:", data);

        let actionName;
        ctis_remaining = [];
        ctis_for_action = []
        if(nodeData["actionNode"]){
            actionName = nodeData["name"];
            if(data["ctis"][actionName] === undefined){
                return;
            }
            ctis_remaining = data["ctis"][actionName].filter(c => !data["ctis_eliminated"][actionName].includes(c["hashId"]));
            ctis_for_action = data["ctis"][actionName];
        }
        console.log("actionName", actionName);
        console.log("ctis for action:", ctis_for_action);
        console.log("ctis for action remaining:", ctis_remaining.length);

        num_ctis_remaining = ctis_remaining.length

        if(nodeData["actionNode"] === undefined){
            console.log(`Node ${nodeId} not an action node.`);
            // If node is not an action node then compute based on all CTIs for this node.
            ctis = [];
            ctis_eliminated = [];
            for(const action in data["ctis"]){
                ctis = ctis.concat(data["ctis"][action]);
                ctis_eliminated = ctis_eliminated.concat(data["ctis_eliminated"][action]);
            }

            // Computing CTIs uniquely eliminated by each action.
            // TODO: Sort this out.
            for(const action in data["ctis"]){
                ctis_for_other_actions = [];
                for(const otherAction in data["ctis"]){
                    if(otherAction !== action){
                        ctis_for_other_actions = ctis_for_other_actions.concat(data["ctis"][otherAction].map(c => c["hashId"]));
                    }
                }

                // console.log("CTIs for other actions:", ctis_for_other_actions);

                // CTIs unique to this action.
                action_unique_ctis = data["ctis"][action].map(c => c["hashId"]).filter(c => !ctis_for_other_actions.includes(c));
                console.log(`Found ${action_unique_ctis.length} unique CTIs for action ${action}.`);
            }

            ctis_for_action = ctis;
            num_ctis_remaining = ctis.length - ctis_eliminated.length;
        }

        var ctipane = document.getElementById("ctiPane");
        var ctiCounter = document.createElement("h3");
        ctiCounter.innerHTML = `Total CTIs: ${ctis_for_action.length}`;
        ctiCounter.innerHTML += `<br>Total CTIs remaining: ${num_ctis_remaining}`;
        ctiCounter.innerHTML += `<br>Apalache proof? ${data["apalache_proof_check"]}`;
        if(data["project_vars"] !== null){
            ctiCounter.innerHTML += `<br>Projected vars: << ${data["project_vars"]} >>`;
        }
        ctipane.appendChild(ctiCounter);

        if(ctis_for_action.length > 0){
            let cti_ind = 0;
            let cti_table = {};
            for(const c of ctis_for_action){
                    cti_table[c["hashId"]] = c;
            }
            console.log("CTI table:", cti_table);

            // for(const cluster_name in data["cti_clusters"]){
                // cluster_cti_ids = data["cti_clusters"][cluster_name];
                // cti_id = data["cti_clusters"][cluster_name][0]
                // cti_obj = cti_table[cti_id];
                cti_obj = ctis_for_action[0];
                console.log("CTIs for action:", ctis_for_action);

                cti_obj = _.sortBy(ctis_for_action, "cost")[0];

                // console.log(cti_obj);
                // console.log(ctis_remaining);

                if(ctis_remaining && ctis_remaining.length > 0){
                    cti_obj = _.sortBy(ctis_remaining, "cost")[0];
                } else{
                    return;
                }

                // If all CTIs from this cluster are eliminated, then continue.
                // if(cluster_cti_ids.every(cid => data["ctis_eliminated"].includes(cid))){
                //     continue;
                // }
            
                // for(const cti_obj of data["ctis_remaining"].slice(0,2)){
                // let cti_obj = data["ctis"][0];
                let cti_text = cti_obj["cti_str"];
                var ctidiv = document.createElement("div");
                ctidiv.classList.add("cti-box");
                var i = 0;
                // ctidiv.innerHTML += `<h2>Cluster: ${cluster_name.split(" ")[0]}</h2>`;
                ctidiv.innerHTML += `<h3>CTI ${cti_ind} (${cti_obj["action_name"]}), cost=${cti_obj["cost"]}</h3>`;
                for(const state of cti_obj["trace"]){
                    ctidiv.innerHTML += `<h4>CTI State ${i}</h4>`;
                    ctidiv.innerHTML += "<pre>";
                    let lineI = 0;
                    // console.log(cti_obj);
                    for(const line of state["state_lines"]){
                        if(data["project_vars"] !== null && data["project_vars"].every(x => !line.includes(x))){
                            continue;
                        }
                        let prevLine = cti_obj["trace"][0]["state_lines"][lineI];
                        let isDiff = i==1 && (prevLine !== line);
                        let color = isDiff ? "blue" : "black";
                        ctidiv.innerHTML += `<span style='color:${color}'>` + line + "</span><br>";
                        lineI += 1;
                    }
                    ctidiv.innerHTML += "</pre>";
                    i += 1;
                }
                ctipane.appendChild(ctidiv);
                cti_ind += 1;
            // }
        }

    });   

    $('#gen-ctis-btn').on('click', function(ev){
        genCtis(currentNodeId);
    })

    $('#gen-ctis-btn-subtree').on('click', function(ev){
        genCtisSubtree(currentNodeId);
    })

    $('#refresh-node-btn').on('click', function(ev){
        // let proof_node_expr = $(this).html();
        // console.log(proof_node_expr);
        // $('.cti-container').hide();
        // $('.cti_' + proof_node_expr).show();
        refreshNode(currentNodeId);
        // console.log("Refreshing proof node '" + currentNodeId + "'");
        // focusOnNode(currentNodeId);
        // $.get(local_server + `/getCtis/${currentNodeId}`, function(data){
        //     console.log(data);

        //     // if(data["ctis"].length > 0){
        //     //     color = "orange";
        //     // }

        //     let color = computeNodeColor(data);
        //     console.log(color);
        //     // let color = "orange";
        //     cy.nodes(`node[name = "${currentNodeId}"]`).style('background-color', color);

        // });   

        // let obj = cy.getElementById(currentNodeId);
        // obj.style({"background-color": "red"});
        // console.log("node obj:", obj);
        // cy.nodes(`node`).style('background-color', 'red');
    })

    $('#add-support-lemma-btn').on('click', function(ev){
            console.log("Prime edge creation.");
            supportLemmaTarget = currentNode;
            $('#add-support-lemma-btn').prop("disabled",true);
    }); 

}

function showCtisForNode(nodeId){
    $.get(local_server + `/getCtis/${nodeId}`, function(data){
        console.log(data);
    });   
}

function addNodeToGraph(proof_graph, node){
    dataVal = { id: node["expr"], name: node["name"] };
    // console.log("node:", node);
    // console.log(dataVal);
    // console.log("Nodes:", cy.nodes());
    style = {
        "background-color": computeNodeColor(node)
    }

    let styleParentBox = {
        "background-color": "#eee",
        "shape": "round-rectangle",
    }

    if(node["expr"] === proof_graph["safety"]){
        style["border-width"] = "6px";
        styleParentBox["border-width"] = "5px";
        style["font-size"] = "20px";
        style["width"] = 45;
        style["height"] = style["width"];
    }

    if(node["apalache_proof_check"]){
        styleParentBox["border-color"] = "green";
    }
    
    // console.log(ctis.length)
    if(!addedNodes.includes(node["expr"])){
        addedNodes.push(node["expr"]);

        let parentNodeBoxId = node["expr"] + "_parent_box";

        // Add parent container box first if needed.
        cy.add({
            group: 'nodes',
            data: {
                id: parentNodeBoxId, 
                // name: node["name"]
                name: "",
                parentBox: true
            },
            style: styleParentBox
        });

        // Add main lemma node.
        cy.add({
            group: 'nodes',
            data: { 
                id: node["expr"], 
                name: node["name"],
                parent: parentNodeBoxId
            },
            position: { x: 200, y: 200 },
            color: "red",
            style: style
        });


        //
        // Add action-specific sub-nodes.
        //

        var ix = 0;
        let child_actions = Object.keys(node["children"])
        console.log("child actions:", child_actions);
        let cti_actions = Object.keys(node["ctis"]);
        console.log("cti actions:", cti_actions);
        for(const action of new Set(cti_actions.concat(child_actions))){
            console.log(action);
            if(node["ctis"][action] && node["ctis"][action].length === 0 && !child_actions.includes(action)){
                continue;
            }
            
            let actname = action.split(" ")[0];
            let nid = node["expr"] + "_" + actname;
            let dataVal = { 
                id: nid, 
                name: actname, 
                actionNode: true,
                parentId: node["name"],
                parent: parentNodeBoxId
            };

            node_size = 18
            cy.add({
                group: 'nodes',
                data: dataVal,
                position: { x: 200, y: 200 },
                color: "red",
                size: 3,
                style: {
                    "background-color": computeNodeColor(node, actname),
                    "shape": "rectangle", 
                    "width": node_size, 
                    "height": node_size,
                    "font-size":"12px"
                },
            });

            let edgeName = nid + "_" + actname + node['expr'];
            cy.add({
                group: 'edges', 
                data: {
                    id: edgeName,
                    source: nid,
                    target: node["expr"],
                    // data: child,
                },
                style: {
                    // "line-color": "gray",
                    "target-arrow-shape": "triangle",
                    "width": 2
                }
            });
            ix += 1;
        }
    }
}

function addNodesToGraph(proof_graph, node){
 
    // Add this node.
    addNodeToGraph(proof_graph, node);

    // Add children as nodes, recursively.
    for(const action in node["children"]){
        for(const child of node["children"][action]){
            addNodesToGraph(proof_graph, child);
        }
    }

    // Also add any global nodes that were not added via recursive graph traversal.
    for(const node of proof_graph["nodes"]){
        addNodeToGraph(proof_graph, node);
    }
}

function addEdgesToGraph(proof_graph, node){

    // actions = node["cti_clusters"].keys;
    // if(Object.keys(node["cti_clusters"]).length === 0){
    //     actions = ["ALL_ACTIONS"];
    // }

    for(const action in node["children"]){
        // continue;
        // console.log("Node:", node["name"]);
        // console.log("Child action:", action);
        for(const child of node["children"][action]){
            addEdgesToGraph(proof_graph, child);
            let edgeName = 'e_' + child["expr"] + "_" + action + "_" + node["expr"];
            let targetId = node["expr"];
            // if(child["parent_action"] !== null && node["ctis"][child["parent_action"]]){
                // console.log(node["parent_action"]);
                // targetId = node["expr"] + "_" + child["parent_action"];
            targetId = node["expr"] + "_" + action;
                // child["parent_action"];
            // }
            if(!addedEdges.includes(edgeName)){
                addedEdges.push(edgeName);
                cy.add({
                    group: 'edges', 
                    data: {
                        id: edgeName,
                        source: child["expr"],
                        target: targetId,
                        targetParentId: node["expr"],
                        targetNode: node,
                        child: child,
                        actionSubEdge: true,
                        action: action 
                    }, 
                    style: {
                        "target-arrow-shape": "triangle",
                        "arrow-scale": 2.0,
                        "line-color": "steelblue",
                        "target-arrow-color": "steelblue"
                    }
                });
            }
        }
    }
}

function reloadProofGraph(onCompleteFn){
    if(cy !== null){
        cy.elements().remove();
        addedNodes = [];
        addedEdges = [];
    }

    // Can double click support edges to delete them from proof graph.
    cy.on('click', 'edge', function(evt){

        if(selectedEdge === null){
            selectedEdge = this;
        } else{
            selectedEdge.style({"line-color":"steelblue", "font-weight": "normal"});
            selectedEdge = this;
        }
        selectedEdge.style({"line-color":"orange", "font-weight": "bold"});
        $('#delete-support-edge-btn').css('visibility', 'visible');
        return

        console.log("double clicked edge");
        let source = this.data()["source"];
        console.log(this.data()["child"]);
        let target = this.data()["targetNode"];
        let action = this.data()["action"];
        let parentId = this.data()["targetParentId"];
        deleteSupportLemmaEdge(target["name"], action, this.data()["child"]["name"])
    });


    cy.on('click', 'node', function(evt){
        console.log( 'clicked ' + this.id() );
        let name = this.data()["name"];
        let nid = this.data()["id"];

        if(selectedEdge !== null){
            selectedEdge.style({"line-color":"steelblue", "font-weight": "normal"});
            selectedEdge = null;
        }


        // Don't do anything for enclosing parent boxes.
        if(this.data()["parentBox"]){
            return;
        }

        console.log("node name:", name, "node id:", nid);
        console.log("parent id", this.data()["parentId"]);
        let actionNode = this.data()["actionNode"];
        
        // Check if we are primed for new support lemma edge creation.
        if(supportLemmaTarget !== null && supportLemmaTarget.data()["actionNode"]){
            console.log("Create support lemma edge:", supportLemmaTarget, name);

            // Add support lemma edge.
            let parentId = supportLemmaTarget.data()["parentId"];
            let action = supportLemmaTarget.data()["name"];
            addSupportLemmaEdge(parentId, action, name);
            supportLemmaTarget = null;
            $('#add-support-lemma-btn').prop("disabled",false);
            return;
            
        }

        focusOnNode(name, this.data());
        if(currentNode !== null){
            currentNode.style({"color":"black", "font-weight": "normal"});
        }
        currentNode = this;
        currentNode.style({"color":"black", "font-weight": "bold"});
    });

    cy.edges('edge').style({
        "curve-style": "straight",
        "target-arrow-shape": "triangle"
    })

    console.log("Fetching proof graph.");

    $.get(local_server + `/getProofGraph`, function(data){
        console.log("proof graph obj:", data);

        let proof_graph = data["proof_graph"];
        let root = data["proof_graph"]["root"];

        // Save any global spec definitions.
        specDefs = proof_graph["spec_defs"];

        addNodesToGraph(proof_graph, root);
        addEdgesToGraph(proof_graph, root);

        cy.edges('edge').style({
            "curve-style": "straight",
            // "line-color": "steelblue",
            "target-arrow-shape": "triangle"
        })

        // let layout = cy.layout({name:"cose"});
        let layout = cy.layout({ 
            name: "dagre", 
            // padding:50,
            // nodeSep: 300.0, 
            // edgeSep: 20.0,
            spacingFactor: 0.8,
            nodeDimensionsIncludeLabels: true,
            transform: function( node, pos ){ 
                return pos;
                // console.log("pos", pos);
                // let parent = node.parent();
                // console.log(parent);
                // if(node.data()["actionNode"]){
                //     pos.x *= 0.1;
                // }
                // return pos; 
            },
            // edgeWeight: function(edge){
            //     // console.log("edge data:", edge.data());
            //     if(edge.data()["actionSubEdge"]){
            //         return 10.0;
            //     } else{
            //         return 0.1;
            //     }
            // }
            });
        layout.run();

        // Callback to run once graph is reloaded.
        if(onCompleteFn !== undefined){
            onCompleteFn();
        }

    });
}

function reloadLayout(){
    // Hide all CTIs initially.
    $('.cti-container').hide();

    $('.proof-node-expr').on('click', function(ev){
        // TODO.
        // $(this).children('ul').eq(1).toggle();
        let proof_node_expr = $(this).html();
        console.log(proof_node_expr);
        $('.cti-container').hide();
        $('.cti_' + proof_node_expr).show();
    })


    var body = document.getElementsByTagName("body");
    var div = document.createElement("div");
    div.id = "stategraph";

    var divcti = document.createElement("div");
    divcti.id = "ctiPane";

    // document.body.appendChild(div);
    document.body.prepend(divcti);
    document.body.prepend(div);

    setCTIPaneHtml();

    cy = cytoscape({
        container: document.getElementById('stategraph'), // container to render in
        wheelSensitivity: 0.1,
        boxSelectionEnabled: false,
        style: [
            {
                selector: 'node',
                style: {
                    'label': function (el) {
                        return el.data()["name"];
                    },
                    "background-color": "lightgray",
                    "border-style": "solid",
                    "border-width": "1",
                    "border-color": "black",
                    "font-size":"14px"
                }
            },
            {
                selector: ':parent',
                css: {
                  'text-valign': 'top',
                  'text-halign': 'center',
                }
            },
            {
                selector: 'edge',
                style: {
                    'label': function (el) {
                        // Disable for now.
                        return "";
                        let eliminated = el.data()["data"]["num_parent_ctis_eliminated"];
                        if(eliminated > 0){
                            return eliminated;
                        }
                    },
                    // "background-color": "lightgray",
                    // "border-style": "solid",
                    // "border-width": "1",
                    // "border-color": "black",
                    "font-size":"10px"
                }
            },
        ]
    });

    reloadProofGraph();
}

window.onload = function(){
    reloadLayout();
}
