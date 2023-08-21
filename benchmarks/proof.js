console.log("hello console");
local_server = "http://127.0.0.1:5000"
currentNodeId = null;
currentNode = null

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
    ctipane.innerHTML += "<button id='gen-ctis-btn'> Gen CTIs </button>";
}

function focusOnNode(nodeId){
    currentNodeId = nodeId;
    setCTIPaneHtml();
    $.get(local_server + `/getCtis/${nodeId}`, function(data){
        console.log("Retrieved CTIs for '" + nodeId + "'");
        console.log(data);

        var ctipane = document.getElementById("ctiPane");
        var ctiCounter = document.createElement("h3");
        ctiCounter.innerHTML = `Total CTIs: ${data["ctis"].length}`;
        var ctiCounter2 = document.createElement("h3");
        console.log("data", data);
        ctiCounter2.innerHTML = `Total CTIs remaining: ${data["ctis_remaining"].length}`;
        ctiCounter2.innerHTML += `<br>Apalache proof? ${data["apalache_proof_check"]}`;
        ctipane.appendChild(ctiCounter);
        ctipane.appendChild(ctiCounter2);

        if(data["ctis"].length > 0){
            let cti_ind = 0;
            for(const cti_obj of data["ctis_remaining"].slice(0,2)){
                // let cti_obj = data["ctis"][0];
                let cti_text = cti_obj["cti_str"];
                var ctidiv = document.createElement("div");
                ctidiv.classList.add("cti-box");
                var i = 0;
                ctidiv.innerHTML += `<h3>CTI ${cti_ind} (${cti_obj["action_name"]}), cost=${cti_obj["cost"]}</h3>`;
                for(const state of cti_obj["trace"]){
                    ctidiv.innerHTML += `<h4>CTI State ${i}</h4>`;
                    ctidiv.innerHTML += "<pre>";
                    let lineI = 0;
                    for(const line of state["state_lines"]){
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

    var cy = cytoscape({
        container: document.getElementById('stategraph'), // container to render in
        wheelSensitivity: 0.1,
        style: [
            {
                selector: 'node',
                style: {
                    'label': function (el) {
                        return el.data()["id"];
                    },
                    "background-color": "lightgray",
                    "border-style": "solid",
                    "border-width": "1",
                    "border-color": "black",
                    "font-size":"14px"
                }
            },
        ]
    });

    cy.on('click', 'node', function(evt){
        console.log( 'clicked ' + this.id() );
        let name = this.data()["name"];
        showCtisForNode(name);
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
        console.log("node:", node);
        // console.log(dataVal);
        // console.log("Nodes:", cy.nodes());
        ctis = node["ctis"];
        ctis_eliminated = node["ctis_eliminated"];
        let style = {"background-color": "orange"}
        if(node["had_ctis_generated"] && ctis.length === ctis_eliminated.length){
            style = {"background-color": "green"}
        }
        if(!node["had_ctis_generated"]){
            style = {"background-color": "lightgray"}
        }
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
        }

        for(const child of node["children"]){
            addNodesToGraph(proof_graph, child);
        }
    }

    let addedEdges = [];
    function addEdgesToGraph(proof_graph, node){
        for(const child of node["children"]){
            addEdgesToGraph(proof_graph, child);
            let edgeName = 'e_' + child["expr"] + node["expr"];
            if(!addedEdges.includes(edgeName)){
                addedEdges.push(edgeName);
                cy.add({
                    group: 'edges', data: {
                        id: edgeName,
                        source: child["expr"],
                        target: node["expr"]
                    }
                });
            }

        }
    }

    console.log("Get proof");
    $.get(local_server + `/getProofGraph`, function(data){
        console.log("return");
        console.log(data);

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
    

        // let layout = cy.layout({name:"cose"});
        let layout = cy.layout({ name: "dagre", nodeSep: 90.0, spacingFactor: 1.6 });
        layout.run();

    });

}
