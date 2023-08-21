import json
import graphviz
import random

f = open("edges.json")
edgeSets = json.load(f)["edges"]
f.close()

G = graphviz.Digraph()
# G.graph_attr.update(size="2,2")  
G.attr(rankdir="TD")
for i,t in enumerate(edgeSets):
    with G.subgraph(name="cluster_" + str(i)) as Gs:
        # Gs.node(f"anchor_{i}", style="invis")
        # Gs.edge(f"anchor_{i}", f"anchor_{(i + 1)}", style="invis")
        print(t)
        for ei,ej in t:
            ei_text = ei.replace("<<", "[").replace(">>", "]")
            ej_text = ej.replace("<<", "[").replace(">>", "]")
            print(f"c{i}_" + ei_text)
            Gs.node(f"c{i}_" + ei_text, ei_text)
            Gs.node(f"c{i}_" + ej_text, ej_text)

        # for ei,ej in t:
        #     ei_text = ei.replace("<<", "(").replace(">>", ")")
        #     ej_text = ej.replace("<<", "(").replace(">>", ")")
        #     print(f"c{i}_" + ei_text)
            Gs.edge(f"c{i}_" + ei_text, f"c{i}_" + ej_text)
G.render("logtrees")


