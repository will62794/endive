console.log("hello console");
local_server = "http://127.0.0.1:5000"
currentNodeId = null;
currentNode = null
cy = null;
let addedNodes = [];
let addedEdges = [];

let awaitPollIntervalMS = 1000;

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
        }
    });
}

function genCtis(exprName){
    console.log("Generating CTIs for '" + exprName + "'");
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

function setCTIPaneHtml(nodeData){
    var ctipane = document.getElementById("ctiPane");
    ctipane.innerHTML = "<h1> CTI View </h1>";
    let nodeIdText = currentNodeId;
    if(nodeData && nodeData["actionNode"]){
        nodeIdText = nodeData["parentId"] + " -> " + currentNodeId + "";
    }
    ctipane.innerHTML += `<h3> Proof node: ${nodeIdText} </h3>`;
    ctipane.innerHTML += "<div><button id='gen-ctis-btn'> Gen CTIs </button></div> <br>";
    ctipane.innerHTML += "<div><button id='gen-ctis-btn-subtree'> Gen CTIs (recursive) </button></div> <br>";
    ctipane.innerHTML += "<div><button id='refresh-node-btn'> Refresh Proof Node </button></div>";
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
        console.log("color ctis:", ctis);
        console.log("color ctis elim:", ctis_eliminated);
    } else{
        ctis = data["ctis"][action];
        ctis_eliminated = data["ctis_eliminated"][action];
    }

    if(data["had_ctis_generated"] && ctis.length === ctis_eliminated.length){
        // style = {"background-color": "green"}
        return "green";
    }
    if(!data["had_ctis_generated"]){
        // style = {"background-color": "lightgray"}
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
        if(nodeData["actionNode"]){
            actionName = nodeData["name"];
            ctis_remaining = data["ctis_remaining"][actionName]
        }
        console.log("actionName", actionName);
        ctis_for_action = data["ctis"][actionName];
        console.log("ctis for action:", ctis_for_action);

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
                    console.log(cti_obj);
                    for(const line of state["state_lines"]){
                        if(data["project_vars"] !== null && data["project_vars"].every(x => !line.includes(x))){
                            continue;
                        }
                        let isDiff = i==1 && (cti_obj["trace"][0]["state_lines"][lineI] !== line);
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
}

function showCtisForNode(nodeId){
    $.get(local_server + `/getCtis/${nodeId}`, function(data){
        console.log(data);
    });   
}


function addNodesToGraph(proof_graph, node){
    dataVal = { id: node["expr"], name: node["name"] };
    // console.log("node:", node);
    // console.log(dataVal);
    // console.log("Nodes:", cy.nodes());
    style = {"background-color": computeNodeColor(node)}
    if(node["expr"] === proof_graph["safety"]){
        style["border-width"] = "5px";
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
                name: node["name"]
            },
            style: {
                "background-color": "#eee",
                "shape": "rectangle", 
                // "width": "100px", 
                // "height": 200
            },
        });

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

            cy.add({
                group: 'nodes',
                data: dataVal,
                position: { x: 200, y: 200 },
                color: "red",
                size: 3,
                style: {
                    "background-color": computeNodeColor(node, actname),
                    "shape": "rectangle", 
                    "width":20, 
                    "height":20,
                    "font-size":"12px"
                },
            });

            let edgeName = actname + node['expr'];
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

    for(const action in node["children"]){
        for(const child of node["children"][action]){
            addNodesToGraph(proof_graph, child);
        }
    }
}

function addEdgesToGraph(proof_graph, node){

    // actions = node["cti_clusters"].keys;
    // if(Object.keys(node["cti_clusters"]).length === 0){
    //     actions = ["ALL_ACTIONS"];
    // }

    for(const action in node["children"]){
        // continue;
        console.log("Node:", node["name"]);
        console.log("Child action:", action);
        for(const child of node["children"][action]){
            addEdgesToGraph(proof_graph, child);
            let edgeName = 'e_' + child["expr"] + node["expr"];
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
                        child: child,
                        actionSubEdge: true
                    }, 
                    style: {
                        "target-arrow-shape": "triangle",
                        "arrow-scale":2.1,
                        "line-color": "steelblue",
                        "target-arrow-color": "steelblue"
                    }
                });
            }
        }
    }
}

function reloadProofGraph(){
    if(cy !== null){
        cy.elements().remove();
        addedNodes = [];
        addedEdges = [];
    }

    cy.on('click', 'node', function(evt){
        console.log( 'clicked ' + this.id() );
        let name = this.data()["name"];
        let nid = this.data()["id"];
        console.log("node name:", name, "node id:", nid);
        console.log("parent id", this.data()["parentId"]);
        let actionNode = this.data()["actionNode"];
        // if(actionNode){
        //     name = this.data()["parentId"]
        // }
        // showCtisForNode(name);
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
        addNodesToGraph(proof_graph, root);
        addEdgesToGraph(proof_graph, root);

        cy.edges('edge').style({
            "curve-style": "straight",
            // "line-color": "steelblue",
            // "target-arrow-color": "steelblue"
        })

        // let layout = cy.layout({name:"cose"});
        let layout = cy.layout({ 
            name: "dagre", 
            // padding:50,
            // nodeSep: 300.0, 
            // edgeSep: 20.0,
            spacingFactor: 1.0,
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
            edgeWeight: function(edge){
                console.log("edge data:", edge.data());
                if(edge.data()["actionSubEdge"]){
                    return 10.0;
                } else{
                    return 0.1;
                }
            }
            });
        layout.run();

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
