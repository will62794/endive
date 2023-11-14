// local_server = "http://127.0.0.1:5000"
// local_server = "http://" + location.host
local_server = ""
cy = null;

currentNodeId = null;
currentNode = null

selectedEdge = null;

generatingCTIs = false;

let addedNodes = [];
let addedEdges = [];
let specDefs = [];

// Stores source node from which to create support lemma edge.
let supportLemmaTarget = null;

let awaitPollIntervalMS = 1000;

cytoscape.warnings(false);

var projectionStats = [];

const loadingIcon = '<i class="fa fa-refresh fa-spin"></i>';

//
// consensus_epr demo proof steps.
//

function consensus_epr_demo1(){
    addLemmaNode("H_UniqueLeaders", function(){
        addSupportLemmaEdge("Safety", "DecideAction", "UniqueLeaders");
    });
}

function consensus_epr_demo2(){
    addLemmaNode("H_DecidedImpliesLeader", function(){
        addSupportLemmaEdge("Safety", "DecideAction", "DecidedImpliesLeader");
    });
}

function consensus_epr_demo3(){
    addLemmaNode("H_LeaderImpliesVotesInQuorum", function(){
        addSupportLemmaEdge("DecidedImpliesLeader", "BecomeLeaderAction", "LeaderImpliesVotesInQuorum");
    });
}

function awaitGenCtiCompletion(expr, onCompleteFn){
    $.get(local_server + `/api/getActiveCtiGenThreads`, function(data){
        console.log("checking active cti threads:", data)

        let active_threads = data["active_threads"];

        let config_ind = data["current_config_instance_ind"];
        let num_config_instances = data["num_config_instances"];
        let ctigen_state = data["ctigen_state"];
        let currHTML = $('#gen-ctis-btn').html().split(" - ")[0];
        let addHTML = ` - Config instance ${config_ind + 1}/${num_config_instances} (${ctigen_state})`;
        $('#gen-ctis-btn').html(currHTML + " " + addHTML);
        $('#gen-ctis-btn').prop("disabled", true);
        $('#gen-ctis-btn-subtree').prop("disabled", true);

        if(active_threads.length > 0){
            setTimeout(() => awaitGenCtiCompletion(expr, onCompleteFn), awaitPollIntervalMS);
        } else{
            // Once active CTI gen thread completes, refresh the proof graph.
            reloadProofGraph(function(){
                $('#gen-ctis-btn').prop("disabled",false);
                $('#gen-ctis-btn-subtree').prop("disabled",false);
                $('#cti-loading-icon').css('visibility', 'hidden');
                // $("#gen-ctis-btn").html("Generate CTIs");
                $("#gen-ctis-btn").html("Check node");
                generatingCTIs = false;
    
                if(onCompleteFn !== undefined){
                    onCompleteFn();
                }
            });

        }
    });
}

// Generate CTIs for a list of multiple nodes.
function genCtisForExprs(exprNameList, onCompleteFn){
    if(generatingCTIs){
        return;
    }

    genCtis(exprNameList[0], function(){
        return genCtisForExprs(exprNameList.splice(1));
    });
}

function genCtisRecursive(exprName){
    traverseProofGraph(exprName, function(visited){
        genCtisForExprs(visited);
    });
}

function genCtis(exprName, onCompleteFn){
    if(generatingCTIs){
        return;
    }

    if(exprName === undefined){
        return;
    }

    console.log("Generating CTIs for '" + exprName + "'");
    $('#cti-loading-icon').css('visibility', 'visible');
    $("#gen-ctis-btn").html("Generating CTIs " + loadingIcon);
    generatingCTIs = true;

    // Mark the node we are actively generating CTIs for.
    let activeStyle = {"border-color": "blue", "border-width": "6px", "background-color": "steelblue"};
    cy.nodes(`node[name = "${exprName}"]`).style(activeStyle);

    $.get(local_server + `/api/genCtis/single/${exprName}`, function(data){
        // console.log(data);
        awaitGenCtiCompletion(exprName, onCompleteFn);
    });
}

function traverseProofGraphRec(startNode, visited){

    console.log("Visiting node:", startNode, startNode["name"]);
    console.log(visited);
    // For each of its children, re-generate CTIs.
    if(visited.includes[startNode["name"]]){
        return [];
    }
    visited.push(startNode["name"]);
    for(const action in startNode["children"]){
        let visitedSubtree = [];
        for(const child of startNode["children"][action]){
            console.log(child["name"]);
            if(!visited.includes(child["name"])){
                visitedSubtree = traverseProofGraphRec(child, visited);
            }
        }
    }
}

function traverseProofGraph(startNodeExprName, onCompleteFn){
    console.log("Traverse proof graph from start node:", startNodeExprName);
    $.get(local_server + `/api/getNode/${startNodeExprName}`, function(data){
        console.log(data);
        let visited = [];
        traverseProofGraphRec(data, visited);
        console.log("visited nodes:", visited);
        onCompleteFn(visited);
    });
}

function addLemmaNode(lemmaName, onCompleteFn){
    console.log("Adding lemma:", lemmaName);
    $.get(local_server + `/api/addNode/${lemmaName}`, function(data){
        reloadProofGraph(onCompleteFn);
    });
}

function deleteSupportLemmaEdge(edge){

    let source = edge.data()["source"];
    let sourceNode = edge.data()["child"];
    let target = edge.data()["targetNode"];
    let action = edge.data()["action"];
    let parentId = edge.data()["targetParentId"];

    console.log("Deleting support edge, target:", target, ", source:", source, ", action: ", action);
    $.get(local_server + `/api/deleteSupportEdge/${target["name"]}/${action}/${sourceNode["name"]}`, function(data){
        // console.log(data);
        // console.log("add edge complete.");

        $('#delete-support-edge-btn').css('visibility', 'hidden');

        // Once we added the new support edge, we should reload the proof graph and re-generate CTIs
        // for the target node.
        reloadProofGraph(function(){
            genCtis(target["name"]);
        });
    });
}

function addSupportLemmaEdge(target, action, src){
    console.log("Adding support edge, target:", target, ", source:", src, ", action: ", action);
    $.get(local_server + `/api/addSupportEdge/${target}/${action}/${src}`, function(data){
        // console.log(data);
        // console.log("add edge complete.");

        if(!data["ok"]){
            console.log("Error when adding lemma support edge.");
            return;
        }

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

    // let generatingCTIsDiv = '<div id="cti-loading-icon">Generating CTIs <i class="fa fa-refresh fa-spin"></i></div>';
    let generatingCTIsDiv = `<div id="cti-loading-icon">Generating CTIs ${loadingIcon}</div>`;
    // ctipane.innerHTML += generatingCTIsDiv;
    ctipane.innerHTML += `<div id='proof-node-name'> Proof node: ${nodeIdText} </div><br>`;

    // For now don't allow CTI generation for specific sub-actions, only for top-level node all at once.
    // ctipane.innerHTML += `<div><button id='gen-ctis-btn'> Generate CTIs </button> ${generatingCTIsDiv}</div> <br>`;
    ctipane.innerHTML += `<div><button id='gen-ctis-btn'> Check node </button></div> <br>`;
    ctipane.innerHTML += "<div><button id='gen-ctis-btn-subtree'> Check node (recursive) </button></div> <br>";

    // ctipane.innerHTML += "<div><button id='refresh-node-btn'> Refresh Proof Node </button></div> <br>";
    ctipane.innerHTML += "<div><button id='add-support-lemma-btn'> Add support lemma </button></div><br>";
    ctipane.innerHTML += "<div><button id='delete-support-edge-btn'> Delete support lemma edge </button></div><br>";

    ctipane.innerHTML += "<div><button id='add-lemma-node-btn'> Add lemma </button></div><br>";

    ctipane.innerHTML += '<label for="lemmas">Choose a lemma node to add:</label><br>';
    let selectHTML = '<select name="lemmas" id="lemma-selection">';
    let defsSorted = specDefs.sort();
    for(const def of defsSorted){
        if(def.startsWith("H_")){
            selectHTML += `<option value="${def}">${def}</option>`;
        }
    }
    selectHTML += '</select>';
    ctipane.innerHTML += selectHTML;

    $("#gen-ctis-btn").prop('disabled', true);
    $("#gen-ctis-btn-subtree").prop('disabled', true);


    if(nodeData && !nodeData["actionNode"]){
        $("#gen-ctis-btn").prop('disabled', false);
        $("#gen-ctis-btn-subtree").prop('disabled', false);
    }


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
    } else{
        ctis = data["ctis"][action];
        ctis_eliminated = data["ctis_eliminated"][action];
    }

    if(data["had_ctis_generated"] && ctis_eliminated && ctis.length === ctis_eliminated.length){
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
    $.get(local_server + `/api/getNode/${nodeId}`, function(data){
        console.log(data);

        let color = computeNodeColor(data);
        cy.nodes(`node[name = "${nodeId}"]`).style('background-color', color);

    });   
}

function focusOnNode(nodeId, nodeData){
    if(currentNodeId === nodeId){
        return;
    }
    console.log("Focus on node:", nodeId, nodeData);
    currentNodeId = nodeId;
    setCTIPaneHtml(nodeData);

    let nodeIdArg = nodeId;
    // For action nodes, we want to get the data for the associated parent node.
    if(nodeData["actionNode"]){
        nodeIdArg = nodeData["parentId"];
    }

    $.get(local_server + `/api/getNode/${nodeIdArg}`, function(data){
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
        console.log(`CTIs for action (${actionName}):`, ctis_for_action);
        console.log("CTIs for action remaining:", ctis_remaining.length);

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
        var ctiCounter = document.createElement("h4");
        ctiCounter.innerHTML = `Total CTIs: ${ctis_for_action.length}`;
        ctiCounter.innerHTML += `<br>Total CTIs remaining: ${num_ctis_remaining}`;
        ctiCounter.innerHTML += `<br>Apalache proof? ${data["apalache_proof_check"]}`;

        if(ctis_for_action.length > 0){
            one_cti_obj = ctis_for_action[0];
            state_var_proj_map = one_cti_obj["trace"][0]["state_var_projection_map"];
            let numVars = Object.keys(state_var_proj_map).length;
            let varsProjected = Object.keys(state_var_proj_map).filter(k => !state_var_proj_map[k]);
            let varsRetained = Object.keys(state_var_proj_map).filter(k => state_var_proj_map[k]);
            ctiCounter.innerHTML += "<br>";
            ctiCounter.innerHTML += `State variables hidden: (${varsProjected.length}/${numVars}): { ${varsProjected} }`;
            ctiCounter.innerHTML += "<br>";
            ctiCounter.innerHTML += `State variables slice:  (${numVars-varsProjected.length}/${numVars}): { ${varsRetained} }`;
        }

        ctipane.appendChild(ctiCounter);

        if(ctis_for_action.length > 0){
            let cti_ind = 0;
            let cti_table = {};
            for(const c of ctis_for_action){
                    cti_table[c["hashId"]] = c;
            }
            console.log("CTI table:", cti_table);

            // ctis_objs = _.sortBy(ctis_for_action, "cost").splice(0,numCtisToShow);
            // console.log("CTIs for action:", ctis_for_action);

            let numCtisToShow = 5;

            if(ctis_remaining && ctis_remaining.length > 0){
                ctis_objs = _.sortBy(ctis_remaining, "cost").splice(0,numCtisToShow);
            } else{
                return;
            }

            // cti_objs = _.sortBy(ctis_for_action, "cost")[0];s
            for(const cti_obj of ctis_objs){

                // cluster_cti_ids = data["cti_clusters"][cluster_name];
                // cti_id = data["cti_clusters"][cluster_name][0]
                // cti_obj = cti_table[cti_id];
                // cti_obj = ctis_for_action[0];
                

                // console.log(cti_obj);
                // console.log(ctis_remaining);

            
                // If all CTIs from this cluster are eliminated, then continue.
                // if(cluster_cti_ids.every(cid => data["ctis_eliminated"].includes(cid))){
                //     continue;
                // }
            
                // for(const cti_obj of data["ctis_remaining"].slice(0,2)){
                // let cti_obj = data["ctis"][0];
                let cti_text = cti_obj["cti_str"];
                var ctidiv = document.createElement("div");
                var preelem = document.createElement("pre");
                ctidiv.classList.add("cti-box");
                var i = 0;
                // ctidiv.innerHTML += `<h2>Cluster: ${cluster_name.split(" ")[0]}</h2>`;
                ctidiv.innerHTML += `<h3>CTI ${cti_ind} (${cti_obj["action_name"]}), cost=${cti_obj["cost"]}</h3>`;
                for(const state of cti_obj["trace"]){
                    ctidiv.innerHTML += `<h4>CTI State ${i}</h4>`;
                    let ctiHTML = ""
                    ctiHTML += "<pre>";
                    let lineI = 0;
                    // console.log(cti_obj);

                    let state_lines_field = "state_lines";
                    let enableProjection = true;
                    if(enableProjection){
                        state_lines_field = "state_lines_action_vars_projected";
                    }

                    for(const line of state[state_lines_field]){
                        let prevLine = cti_obj["trace"][0][state_lines_field][lineI];
                        let isDiff = i==1 && (prevLine !== line);
                        let color = isDiff ? "blue" : "black";
                        // let escapedLine = line.trim().replaceAll("<", "&lt;").replaceAll(">", "&gt;");
                        let escapedLine = line.replaceAll("<", "&lt;").replaceAll(">", "&gt;");
                        // Replace excessive whitespace.
                        

                        escapedLine = escapedLine.replaceAll("                       ", "\n&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;");
                        escapedLine = escapedLine.replaceAll("                      ", "\n&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ");
                        escapedLine = escapedLine.replaceAll("                     ", "\n&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ");
                        escapedLine = escapedLine.replaceAll("                  ", "\n&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ");
                        escapedLine = escapedLine.replaceAll("             ", "\n&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ");
                        escapedLine = escapedLine.replaceAll("       ", "\n&nbsp;&nbsp;&nbsp; ");
                        // escapedLine = escapedLine.replaceAll("      ", "\n&nbsp;&nbsp; ");
                        // escapedLine = escapedLine.replaceAll("     ", "\n&nbsp;&nbsp;&nbsp; ");
                        // escapedLine = escapedLine.replaceAll("    ", "\n&nbsp;&nbsp;&nbsp; ");

                        let maxLineLen = 100;
                        let added = 0;
                        // if(escapedLine.length > maxLineLen){
                        //     while(added < escapedLine.length){
                        //         let subline = escapedLine.substr(added, maxLineLen);
                        //         console.log("subline:", subline);
                        //         let space = "";
                        //         if(added > 0){
                        //             space = "    "
                        //         }
                        //         ctiHTML += `<span style='color:${color}'>` + space + subline + "</span><br>";
                        //         added += maxLineLen;
                        //     }
                        // } 
                        // else{
                            ctiHTML += `<span style='color:${color}'>` + escapedLine + "</span><br>";
                        // }
                        lineI += 1;
                    }
                    ctiHTML += "</pre>";
                    // console.log(ctiHTML);
                    ctidiv.innerHTML += ctiHTML;
                    i += 1;
                }
                ctipane.appendChild(ctidiv);
                cti_ind += 1;
            // }
        }
    }

    });   

    $('#gen-ctis-btn').on('click', function(ev){
        genCtis(currentNodeId);
    })

    $('#gen-ctis-btn-subtree').on('click', function(ev){
        genCtisRecursive(currentNodeId);
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
    $.get(local_server + `/api/getCtis/${nodeId}`, function(data){
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

        // style['label'] = function(data){
        //     return "x";
        // }

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
        // console.log("child actions:", child_actions);
        let cti_actions = Object.keys(node["ctis"]);
        // console.log("cti actions:", cti_actions);
        for(const action of new Set(cti_actions.concat(child_actions))){
            // console.log(action);
            if(node["ctis"][action] && node["ctis"][action].length === 0 && !child_actions.includes(action)){
                continue;
            }

            let actionvars = proof_graph["vars_in_action"][action];
            let lemmavars = proof_graph["vars_in_lemma_defs"][node["expr"]];
            // console.log("actionvars:", actionvars);
            // console.log("lemmavars:", lemmavars);
            let localvars = _.union(actionvars, lemmavars);
            projectionStats.push(localvars);
            
            let actname = action.split(" ")[0];
            let nid = node["expr"] + "_" + actname;
            let dataVal = { 
                id: nid, 
                name: actname, 
                actionNode: true,
                parentId: node["name"],
                parent: parentNodeBoxId,
                localvars: localvars
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
                    "font-size":"12px",
                    // "label": function(data){
                    //     return "x";
                    // }
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
                    actionSubnodeEdge: true,
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
                // console.log("Adding edge from node:", node);

                let actionvars = proof_graph["vars_in_action"][action];
                let lemmavars = proof_graph["vars_in_lemma_defs"][node["expr"]];
                // console.log("actionvars:", actionvars);
                // console.log("lemmavars:", lemmavars);
                let localvars = _.union(actionvars, lemmavars);
                projectionStats.push(localvars);

                cy.add({
                    group: 'edges', 
                    data: {
                        id: edgeName,
                        source: child["expr"],
                        target: targetId,
                        targetParentId: node["expr"],
                        ctis_eliminated_uniquely: node["ctis_eliminated_uniquely"],
                        targetNode: node,
                        child: child,
                        action: action,
                    }, 
                    style: {
                        "target-arrow-shape": "triangle",
                        "arrow-scale": 2.0,
                        // "line-color": "steelblue",
                        // "target-arrow-color": "steelblue"
                    }
                });
            }
        }
    }
}

function onNodeSelect(node){
    console.log( 'clicked ' + node.id() );
    let name = node.data()["name"];
    let nid = node.data()["id"];

    if(selectedEdge !== null){
        selectedEdge.style({"line-color":"steelblue", "font-weight": "normal", "target-arrow-color": "steelblue"});
        selectedEdge = null;
    }


    // Don't do anything for enclosing parent boxes.
    if(node.data()["parentBox"]){
        return;
    }

    console.log("node name:", name, "node id:", nid);
    console.log("parent id", node.data()["parentId"]);
    let actionNode = node.data()["actionNode"];
    
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

    focusOnNode(name, node.data());
    if(currentNode !== null){
        currentNode.style({"color":"black", "font-weight": "normal"});
    }
    currentNode = node;
    currentNode.style({"color":"black", "font-weight": "bold"});
}

function reloadProofGraph(onCompleteFn){
    if(cy !== null){
        cy.elements().remove();
        addedNodes = [];
        addedEdges = [];
    }

    // Can double click support edges to delete them from proof graph.
    cy.on('click', 'edge', function(evt){
        if(this.data()["actionSubnodeEdge"]){
            // Action node edges are not selectable.
            return;
        }


        if(selectedEdge === null){
            selectedEdge = this;
        } else{
            selectedEdge.style({
                "line-color":"steelblue", 
                "target-arrow-color": "steelblue",
                "font-weight": "normal",
            });
            selectedEdge = this;
        }
        selectedEdge.style({
            "line-color":"orange", 
            "font-weight": "bold",
            "target-arrow-color": "orange"
        });

        $('#delete-support-edge-btn').css('visibility', 'visible');
        $('#delete-support-edge-btn').html(`Delete support lemma edge: <span class='monofont'>${this.data()["source"]}</span>`);
        return

        console.log("double clicked edge");
        let source = this.data()["source"];
        console.log(this.data()["child"]);
        let target = this.data()["targetNode"];
        let action = this.data()["action"];
        let parentId = this.data()["targetParentId"];
        deleteSupportLemmaEdge(target["name"], action, this.data()["child"]["name"])
    });


    // Allow double-click on node to also start CTI generation.
    cy.on('dblclick', 'node', function(evt){
        onNodeSelect(this);
        // Don't generate CTIs for action nodes.
        if(this.data()["actionNode"]){
            return;
        }
        genCtis(currentNodeId);
        return;
    })

    cy.on('click', 'node', function(evt){
        onNodeSelect(this);
        return;
    });

    cy.edges('edge').style({
        "curve-style": "straight",
        "target-arrow-shape": "triangle"
    })

    console.log("Fetching proof graph.");

    $.get(local_server + `/api/getProofGraph`, function(data){
        console.log("proof graph obj:", data);

        let proof_graph = data["proof_graph"];
        let root = data["proof_graph"]["root"];

        // Save any global spec definitions.
        specDefs = proof_graph["spec_defs"];

        projectionStats = [];

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

    function edgeColor(el){
        let data = el.data();
        if(data["actionSubnodeEdge"]){
            return "gray";
        } else{
            let ctis_uniquely_eliminated = data["ctis_eliminated_uniquely"];
            if(ctis_uniquely_eliminated.hasOwnProperty(data["action"])){
                let unique_ctis = ctis_uniquely_eliminated[data["action"]][data["child"]["name"]]
                if(unique_ctis === undefined){
                    return "steelblue";
                }
                if(unique_ctis.length === 0){
                    return "maroon";
                }
            }
            return "steelblue";
        }        
    }

    // Optionally show variables underneath action node name.
    // let includeVars = true;
    let includeVars = false;

    cy = cytoscape({
        container: document.getElementById('stategraph'), // container to render in
        wheelSensitivity: 0.1,
        boxSelectionEnabled: false,
        style: [
            {
                selector: 'node',
                style: {
                    'label': function (el) {
                        if(el.data()["actionNode"]){
                            let lbl = el.data()["name"] 
                            if(includeVars){
                                lbl += "\n" + "{" + el.data()["localvars"].join(", ") + "}";
                            }
                            return lbl;
                        }
                        return el.data()["name"] + "";
                    },
                    "text-wrap": "wrap",
                    "background-color": "lightgray",
                    "border-style": "solid",
                    "border-width": "1",
                    "border-color": "black",
                    "font-size":"13px"
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
                        // Show number of uniquely eliminated CTIs on incoming support edges.
                        let data = el.data();
                        if(data["actionSubnodeEdge"]){
                            return "";
                        }
                        let ctis_uniquely_eliminated = data["ctis_eliminated_uniquely"];
                        if(ctis_uniquely_eliminated.hasOwnProperty(data["action"])){
                            let unique_ctis = ctis_uniquely_eliminated[data["action"]][data["child"]["name"]]
                            if(unique_ctis === undefined){
                                return "";
                            }
                            return unique_ctis.length + " unique CTIs";
                        }
                    },
                    "color": edgeColor,
                    // "line-color": edgeColor,
                    // "target-arrow-color": edgeColor,
                    "line-width": "1",
                    "font-size":"10px"
                }
            },
        ]
    });

    reloadProofGraph();


    // Build legend for proof graph.
    let stategraph = document.getElementById('stategraph');
    var legendDiv = document.createElement("div");
    legendDiv.id = "graph-legend";
    legendDiv.innerHTML = "";
    legendDiv.innerHTML += `<ul id="legend-list">`;
    legendDiv.innerHTML += `<li>&#9711; Lemma node<br></li>`;
    legendDiv.innerHTML += `<li><span style='font-size:18px'>&#9633;</span> Action subnode<br></li>`;
    legendDiv.innerHTML += `<li><i class="fa fa-circle proven-color"></i> Proved<br></li>`;
    legendDiv.innerHTML += `<li><i class="fa fa-circle ctis-left-color"></i> Unproven (CTIs remaining)<br><br></li>`;
    legendDiv.innerHTML += `<li>(Click on edge to delete support lemma)<br></li>`;
    legendDiv.innerHTML += `<li>(Double click lemma node to re-generate CTIs)</li>`;
    legendDiv.innerHTML += `</ul>`;
    // stategraph.appendChild(legendDiv);

}

window.onload = function(){
    reloadLayout();
}
