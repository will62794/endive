console.log("hello console");

window.onload = function(){
    $('li').on('click', function(ev){
        // TODO.
        // $(this).children('ul').eq(1).toggle();
        // console.log($(this).children('ul').eq(0));
    })


    $('.proof-node-expr').on('click', function(ev){
        // TODO.
        // $(this).children('ul').eq(1).toggle();
        let proof_node_expr = $(this).html();
        console.log(proof_node_expr);
        $('.cti-box').hide();
        $('.cti_' + proof_node_expr).show();
    })
}
