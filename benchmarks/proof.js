console.log("hello console");
local_server = "http://127.0.0.1:5000"

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
    document.body.appendChild(div);

    var cy = cytoscape({
        container: document.getElementById('stategraph'), // container to render in
        style: [
            {
                selector: 'node',
                style: {
                    'label': function (el) {
                        return JSON.stringify(el.data()["state"]);
                    },
                    "background-color": "lightgray",
                    "border-style": "solid",
                    "border-width": "1",
                    "border-color": "black"
                }
            },
        ]
    });

    // nodes = [1,2,3];
    // for (const node of nodes) {
    //     dataVal = { id: node, state: node };
    //     console.log(dataVal);
    //     cy.add({
    //         group: 'nodes',
    //         data: dataVal,
    //         position: { x: 200, y: 200 }
    //     });
    // }

    // cy.add({
    //     group: 'edges', data: {
    //         id: 'e1',
    //         source: 1,
    //         target: 2
    //     }
    // });

    // cy.add({
    //     group: 'edges', data: {
    //         id: 'e2',
    //         source: 2,
    //         target: 3
    //     }
    // });

    cy.edges('edge').style({
        "curve-style": "straight",
        "target-arrow-shape": "triangle"
    })


    let addedNodes = [];
    function addNodesToGraph(node){
        dataVal = { id: node["expr"], state: node["expr"] };
        console.log(dataVal);
        console.log("Nodes:", cy.nodes());
        if(!addedNodes.includes(node["expr"])){
            addedNodes.push(node["expr"]);
            cy.add({
                group: 'nodes',
                data: dataVal,
                position: { x: 200, y: 200 }
            });
        }

        for(const child of node["children"]){
            addNodesToGraph(child);
        }
    }

    let addedEdges = [];
    function addEdgesToGraph(node){
        for(const child of node["children"]){
            addEdgesToGraph(child);
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


        let root = data["proof_graph"]["root"];
        addNodesToGraph(root);
        addEdgesToGraph(root);

        cy.edges('edge').style({
            "curve-style": "straight",
            "target-arrow-shape": "triangle",
            "arrow-scale":1.5,
            "line-color": "steelblue",
            "target-arrow-color": "steelblue"
        })
    

        // let layout = cy.layout({name:"cose"});
        let layout = cy.layout({ name: "dagre", nodeSep:50.0, spacingFactor:1.5 });
        layout.run();

    });

}
