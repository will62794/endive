console.log("hello console");
local_server = "http://127.0.0.1:5000"
currentNodeId = null;
currentNode = null
cy = null;

function genCtis(exprName){
    console.log("Gen CTIs", exprName);
    $.get(local_server + `/genCtis/single/${exprName}`, function(data){
        console.log(data);
    });
}

function genCtisSubtree(exprName){
    console.log("Gen CTIs subtree", exprName);
    $.get(local_server + `/genCtis/subtree/${exprName}`, function(data){
        console.log(data);
    });
}

function setCTIPaneHtml(){
    var ctipane = document.getElementById("ctiPane");
    ctipane.innerHTML = "<h1> CTI View </h1>";
    ctipane.innerHTML += `<h3> Proof node: ${currentNodeId} </h3>`;
    ctipane.innerHTML += "<div><button id='gen-ctis-btn'> Gen CTIs </button></div> <br>";
    ctipane.innerHTML += "<div><button id='refresh-node-btn'> Refresh Proof Node </button></div>";
}

function computeNodeColor(data){
    ctis = data["ctis"];
    ctis_eliminated = data["ctis_eliminated"];
    let style = {"background-color": "orange"}
    if(data["had_ctis_generated"] && ctis.length === ctis_eliminated.length){
        // style = {"background-color": "green"}
        return "green";
    }
    if(!data["had_ctis_generated"]){
        // style = {"background-color": "lightgray"}
        return "lightgray";
    }
    return "orange";
}


function refreshNode(nodeId){
    console.log("Refreshing proof node '" + nodeId + "'");
    focusOnNode(nodeId);
    $.get(local_server + `/getNode/${nodeId}`, function(data){
        console.log(data);

        let color = computeNodeColor(data);
        console.log(color);
        // let color = "orange";
        cy.nodes(`node[name = "${nodeId}"]`).style('background-color', color);

    });   
}

function focusOnNode(nodeId){
    currentNodeId = nodeId;
    setCTIPaneHtml();
    $.get(local_server + `/getNode/${nodeId}`, function(data){
        console.log("Retrieved CTIs for '" + nodeId + "'");
        console.log(data);

        var ctipane = document.getElementById("ctiPane");
        var ctiCounter = document.createElement("h3");
        ctiCounter.innerHTML = `Total CTIs: ${data["ctis"].length}`;
        ctiCounter.innerHTML += `<br>Total CTIs remaining: ${data["ctis_remaining"].length}`;
        ctiCounter.innerHTML += `<br>Apalache proof? ${data["apalache_proof_check"]}`;
        if(data["project_vars"] !== null){
            ctiCounter.innerHTML += `<br>Projected vars: << ${data["project_vars"]} >>`;
        }
        ctipane.appendChild(ctiCounter);

        if(data["ctis"].length > 0){
            let cti_ind = 0;
            let cti_table = {};
            for(const c of data["ctis"]){
                cti_table[c["hashId"]] = c;
            }
            console.log("CTI table:", cti_table);

            for(const cluster_name in data["cti_clusters"]){
                cluster_cti_ids = data["cti_clusters"][cluster_name];
                cti_id = data["cti_clusters"][cluster_name][0]
                cti_obj = cti_table[cti_id];

                // If all CTIs from this cluster are eliminated, then continue.
                if(cluster_cti_ids.every(cid => data["ctis_eliminated"].includes(cid))){
                    continue;
                }
            
                // for(const cti_obj of data["ctis_remaining"].slice(0,2)){
                // let cti_obj = data["ctis"][0];
                let cti_text = cti_obj["cti_str"];
                var ctidiv = document.createElement("div");
                ctidiv.classList.add("cti-box");
                var i = 0;
                ctidiv.innerHTML += `<h2>Cluster: ${cluster_name.split(" ")[0]}</h2>`;
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
            }
        }

    });   

    $('#gen-ctis-btn').on('click', function(ev){
        // let proof_node_expr = $(this).html();
        // console.log(proof_node_expr);
        // $('.cti-container').hide();
        // $('.cti_' + proof_node_expr).show();
        console.log("Generating CTIs for '" + currentNodeId + "'");

        $.get(local_server + `/genCtis/single/${currentNodeId}`, function(data){
            console.log(data);
        });   
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

window.onload = function(){
    $('li').on('click', function(ev){
        // TODO.
        // $(this).children('ul').eq(1).toggle();
        // console.log($(this).children('ul').eq(0));
    })

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

    cy.on('click', 'node', function(evt){
        console.log( 'clicked ' + this.id() );
        let name = this.data()["name"];
        // showCtisForNode(name);
        focusOnNode(name);
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


    let addedNodes = [];
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
            cy.add({
                group: 'nodes',
                data: dataVal,
                position: { x: 200, y: 200 },
                color: "red",
                style: style
            });

            var ix = 0;
            for(const action in node["ctis"]){
                if(node["ctis"][action].length === 0){
                    continue;
                }
                
                // node["cti_clusters"][act]
                let actname = action.split(" ")[0];
                let nid = node["expr"] + "_" + actname;
                let dataVal = { id: nid, name: actname };

                cy.add({
                    group: 'nodes',
                    data: dataVal,
                    position: { x: 200, y: 200 },
                    color: "red",
                    size: 3,
                    style: {"background-color": "gray", "shape": "rectangle", "width":20, "height":20}
                });

                let edgeName = actname + node['expr'];
                cy.add({
                    group: 'edges', data: {
                        id: edgeName,
                        source: nid,
                        target: node["expr"],
                        // data: child
                    }
                });
                ix += 1;
            }
        }

        for(const child of node["children"]){
            addNodesToGraph(proof_graph, child);
        }
    }

    let addedEdges = [];
    function addEdgesToGraph(proof_graph, node){
        console.log("Adding edges to graph.");
        console.log(node["cti_clusters"]);

        // actions = node["cti_clusters"].keys;
        // if(Object.keys(node["cti_clusters"]).length === 0){
        //     actions = ["ALL_ACTIONS"];
        // }

        // for(const act in actions){
            // node["cti_clusters"][act]
            // actname = act.split(" ")[0];
            // console.log("child action node:", node["expr"]+"_"+actname);

            for(const child of node["children"]){
                addEdgesToGraph(proof_graph, child);
                let edgeName = 'e_' + child["expr"] + node["expr"];
                if(!addedEdges.includes(edgeName)){
                    addedEdges.push(edgeName);
                    cy.add({
                        group: 'edges', data: {
                            id: edgeName,
                            source: child["expr"],
                            // target: node["expr"],
                            target: node["expr"],
                            //  + "_" + actname,
                            data: child
                        }
                    });
                }

            }
        // }
    }

    console.log("Get proof");
    $.get(local_server + `/getProofGraph`, function(data){
        console.log("proof graph obj:", data);
        // console.log(data);

        let proof_graph = data["proof_graph"];
        let root = data["proof_graph"]["root"];
        addNodesToGraph(proof_graph, root);
        addEdgesToGraph(proof_graph, root);

        cy.edges('edge').style({
            "curve-style": "straight",
            "target-arrow-shape": "triangle",
            "arrow-scale":1.5,
            "line-color": "steelblue",
            "target-arrow-color": "steelblue"
        })

        // cy.nodes('node').style({'background-color': 'red'});

    

        // let layout = cy.layout({name:"cose"});
        let layout = cy.layout({ 
            name: "dagre", 
            nodeSep: 10.0, 
            edgeSep: 20.0,
            spacingFactor: 1.4,
            nodeDimensionsIncludeLabels: true
         });
        layout.run();

    });

}
