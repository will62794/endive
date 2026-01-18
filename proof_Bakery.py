from proofs import *

#
# basic_consensus proof structure.
#

def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")


# H_Inv4690_2f61_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARI] = "cs")) \/ (~(pc[VARJ] = "w1"))
# H_Inv4520_48f3_R1_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI})))
# H_Inv24959_7f87_R1_1_I2 == \A VARJ \in Procs : (pc[VARJ] = "e2") \/ ((unchecked[VARJ] = {})) \/ ((pc[VARJ] \in {"w1","w2"}))
# H_Inv5819_32cd_R1_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARI] = "cs") \/ (~(pc[VARJ] = "w2")))
# H_Inv4576_59b1_R1_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "cs")) \/ (~(pc[VARJ] = "w2"))
# H_Inv4521_3f08_R1_1_I2 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] = "cs"))
# H_Inv10_8778_R2_0_I3 == \A VARJ \in Procs : ~(VARJ \in unchecked[VARJ])
# H_Inv5742_3d78_R2_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "w2"))) \/ (~(pc[VARJ] = "w2"))
# H_Inv80_b6ff_R2_0_I3 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] \in {"w1","w2"}))
# H_Inv1922_5e75_R2_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1")))) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI}))
# H_Inv4606_2f6b_R5_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] \in {"e4","w1","w2"})) \/ (~(pc[VARJ] = "cs"))
# H_Inv11_3838_R8_0_I2 == \A VARI \in Procs : ~(VARI \in unchecked[VARI])
# H_Inv61_df69_R8_0_I2 == \A VARI \in Procs : (nxt[VARI] \in unchecked[VARI]) \/ (~(pc[VARI] = "w2"))
# H_Inv1028_6ea5_R8_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1")))) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>))
# H_Inv140_f68c_R9_0_I1 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] = "e4"))
# H_Inv4227_eecc_R10_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(pc[VARI] \in {"e4","w1","w2"}))
# H_Inv32498_2818_R11_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e3") \/ (~(pc[VARJ] = "cs")))
# H_Inv2740_e784_R16_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(max[VARI] < num[VARJ])) \/ (~(pc[VARI] = "e3")) \/ (~(pc[VARJ] \in {"w1","w2"}))
# H_Inv3293_1a1e_R17_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[VARI]) \/ (~(pc[VARI] = "e2")) \/ (~(pc[VARJ] = "cs")) \/ (~(max[VARI] < num[VARJ]))
# H_Inv0_b3ba_R18_0_I0 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"})))
# H_Inv6093_1c74_R18_1_I2 == \A VARI \in Procs : (max[nxt[VARI]] >= num[VARI]) \/ (~((pc[nxt[VARI]] = "e3"))) \/ (~(pc[VARI] = "w2"))
# H_Inv19_037d_R19_0_I1 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"}))) \/ (~(unchecked[VARI] = {}))
# H_Inv1_b58a_R20_0_I1 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"}))) \/ ((VARJ \in unchecked[VARI]))
# H_Inv350_b077_R20_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"}))) \/ (~(nxt[VARI] = VARJ)) \/ (~(pc[VARI] = "w2"))
# H_Inv103_c9b1_R21_1_I1 == \A VARJ \in Procs : (flag[VARJ]) \/ (~(pc[VARJ] = "e3"))
# H_Inv40_180c_R24_0_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e2"))


#
# Proof nodes.
#

Safety = make_node("Safety")
H_Inv4690_2f61_R0_0_I2 = make_node("H_Inv4690_2f61_R0_0_I2")
H_Inv4520_48f3_R1_0_I2 = make_node("H_Inv4520_48f3_R1_0_I2")
H_Inv24959_7f87_R1_1_I2 = make_node("H_Inv24959_7f87_R1_1_I2")
H_Inv5819_32cd_R1_1_I2 = make_node("H_Inv5819_32cd_R1_1_I2")
H_Inv4576_59b1_R1_1_I2 = make_node("H_Inv4576_59b1_R1_1_I2")
H_Inv4521_3f08_R1_1_I2 = make_node("H_Inv4521_3f08_R1_1_I2")
H_Inv10_8778_R2_0_I3 = make_node("H_Inv10_8778_R2_0_I3")
H_Inv5742_3d78_R2_0_I3 = make_node("H_Inv5742_3d78_R2_0_I3")
H_Inv80_b6ff_R2_0_I3 = make_node("H_Inv80_b6ff_R2_0_I3")
H_Inv1922_5e75_R2_0_I3 = make_node("H_Inv1922_5e75_R2_0_I3")
H_Inv4606_2f6b_R5_0_I2 = make_node("H_Inv4606_2f6b_R5_0_I2")
H_Inv11_3838_R8_0_I2 = make_node("H_Inv11_3838_R8_0_I2")
H_Inv61_df69_R8_0_I2 = make_node("H_Inv61_df69_R8_0_I2")
H_Inv1028_6ea5_R8_0_I2 = make_node("H_Inv1028_6ea5_R8_0_I2")
H_Inv140_f68c_R9_0_I1 = make_node("H_Inv140_f68c_R9_0_I1")
H_Inv4227_eecc_R10_0_I3 = make_node("H_Inv4227_eecc_R10_0_I3")
H_Inv32498_2818_R11_0_I2 = make_node("H_Inv32498_2818_R11_0_I2")
H_Inv2740_e784_R16_0_I3 = make_node("H_Inv2740_e784_R16_0_I3")
H_Inv3293_1a1e_R17_0_I3 = make_node("H_Inv3293_1a1e_R17_0_I3")
H_Inv0_b3ba_R18_0_I0 = make_node("H_Inv0_b3ba_R18_0_I0")
H_Inv6093_1c74_R18_1_I2 = make_node("H_Inv6093_1c74_R18_1_I2")
H_Inv19_037d_R19_0_I1 = make_node("H_Inv19_037d_R19_0_I1")
H_Inv1_b58a_R20_0_I1 = make_node("H_Inv1_b58a_R20_0_I1")
H_Inv350_b077_R20_1_I2 = make_node("H_Inv350_b077_R20_1_I2")
H_Inv103_c9b1_R21_1_I1 = make_node("H_Inv103_c9b1_R21_1_I1")
H_Inv40_180c_R24_0_I1 = make_node("H_Inv40_180c_R24_0_I1")





#   [
#     "Inv4520_48f3_R1_0_I2",
#     "Inv4690_2f61_R0_0_I2_w1bAction"
#   ],
#   [
#     "Inv24959_7f87_R1_1_I2",
#     "Inv4690_2f61_R0_0_I2_w2Action"
#   ],
#   [
#     "Inv5819_32cd_R1_1_I2",
#     "Inv4690_2f61_R0_0_I2_w2Action"
#   ],
#   [
#     "Inv4576_59b1_R1_1_I2",
#     "Inv4690_2f61_R0_0_I2_w2Action"
#   ],
H_Inv4690_2f61_R0_0_I2.children = {
    "w2Action": [ H_Inv4576_59b1_R1_1_I2, H_Inv24959_7f87_R1_1_I2, H_Inv5819_32cd_R1_1_I2 ],
    "w1bAction": [H_Inv4520_48f3_R1_0_I2]
}


#   [
#     "Inv1922_5e75_R2_0_I3",
#     "Inv4520_48f3_R1_0_I2_w2Action"
#   ],
#   [
#     "Inv10_8778_R2_0_I3",
#     "Inv4520_48f3_R1_0_I2_w2Action"
#   ],
#   [
#     "Inv80_b6ff_R2_0_I3",
#     "Inv4520_48f3_R1_0_I2_w2Action"
#   ],
H_Inv4520_48f3_R1_0_I2.children = {
    "w2Action": [H_Inv10_8778_R2_0_I3, H_Inv5742_3d78_R2_0_I3, H_Inv4521_3f08_R1_1_I2, H_Inv1922_5e75_R2_0_I3]
}



#   [
#     "Inv4690_2f61_R0_0_I2",
#     "Inv5819_32cd_R1_1_I2_w1aAction"
#   ],
#   [
#     "Inv4520_48f3_R1_0_I2",
#     "Inv5819_32cd_R1_1_I2_w1bAction"
#   ],

H_Inv5819_32cd_R1_1_I2.children = {
    "w1aAction": [H_Inv4520_48f3_R1_0_I2],
    "w1bAction": [H_Inv4520_48f3_R1_0_I2]
}

#   [
#     "Inv4606_2f6b_R5_0_I2",
#     "Inv4576_59b1_R1_1_I2_w1aAction"
#   ],
#   [
#     "Inv1922_5e75_R2_0_I3",
#     "Inv4576_59b1_R1_1_I2_w1bAction"
#   ],
H_Inv4576_59b1_R1_1_I2.children = {
    "w1aAction": [H_Inv4606_2f6b_R5_0_I2],
    "w1bAction": [H_Inv1922_5e75_R2_0_I3]
}


#   [
#     "Inv80_b6ff_R2_0_I3",
#     "Inv4521_3f08_R1_1_I2_w1bAction"
#   ],
H_Inv4521_3f08_R1_1_I2.children = {
    "w1bAction": [H_Inv80_b6ff_R2_0_I3]
}







#   [
#     "Inv11_3838_R8_0_I2",
#     "Inv5742_3d78_R2_0_I3_w1aAction"
#   ],
#   [
#     "Inv61_df69_R8_0_I2",
#     "Inv5742_3d78_R2_0_I3_w1aAction"
#   ],
#   [
#     "Inv1922_5e75_R2_0_I3",
#     "Inv5742_3d78_R2_0_I3_w1aAction"
#   ],
#   [
#     "Inv1028_6ea5_R8_0_I2",
#     "Inv5742_3d78_R2_0_I3_w1aAction"
#   ],
H_Inv5742_3d78_R2_0_I3.children = {
    "w1aAction": [H_Inv11_3838_R8_0_I2, H_Inv61_df69_R8_0_I2, H_Inv1922_5e75_R2_0_I3, H_Inv1028_6ea5_R8_0_I2]
}


#   [
#     "Inv140_f68c_R9_0_I1",
#     "Inv80_b6ff_R2_0_I3_e4bAction"
#   ],
H_Inv80_b6ff_R2_0_I3.children = {
    "e4bAction": [H_Inv140_f68c_R9_0_I1]
}





#   [
#     "Inv4227_eecc_R10_0_I3",
#     "Inv1922_5e75_R2_0_I3_e4bAction"
#   ],
#   [
#     "Inv80_b6ff_R2_0_I3",
#     "Inv1922_5e75_R2_0_I3_w2Action"
#   ],
#   [
#     "Inv4227_eecc_R10_0_I3",
#     "Inv1922_5e75_R2_0_I3_w2Action"
#   ],
H_Inv1922_5e75_R2_0_I3.children = {
    "e4bAction": [H_Inv4227_eecc_R10_0_I3],
    "w2Action": [H_Inv80_b6ff_R2_0_I3],
    "w2Action": [H_Inv4227_eecc_R10_0_I3]
}



#   [
#     "Inv32498_2818_R11_0_I2",
#     "Inv4606_2f6b_R5_0_I2_e3bAction"
#   ],
#   [
#     "Inv4227_eecc_R10_0_I3",
#     "Inv4606_2f6b_R5_0_I2_w1bAction"
#   ],
H_Inv4606_2f6b_R5_0_I2.children = {
    "e3bAction": [H_Inv32498_2818_R11_0_I2],
    "w1bAction": [H_Inv4227_eecc_R10_0_I3]
}



#   [
#     "Inv4227_eecc_R10_0_I3",
#     "Inv1028_6ea5_R8_0_I2_e4bAction"
#   ],
#   [
#     "Inv4227_eecc_R10_0_I3",
#     "Inv1028_6ea5_R8_0_I2_w2Action"
#   ],
#   [
#     "Inv80_b6ff_R2_0_I3",
#     "Inv1028_6ea5_R8_0_I2_w2Action"
#   ],
H_Inv1028_6ea5_R8_0_I2.children = {
    "e4bAction": [H_Inv4227_eecc_R10_0_I3],
    "w2Action": [H_Inv80_b6ff_R2_0_I3],
    "w1bAction": [H_Inv4227_eecc_R10_0_I3]
}



#   [
#     "Inv2740_e784_R16_0_I3",
#     "Inv4227_eecc_R10_0_I3_e3bAction"
#   ],
#   [
#     "Inv11_3838_R8_0_I2",
#     "Inv4227_eecc_R10_0_I3_w2Action"
#   ],
#   [
#     "Inv80_b6ff_R2_0_I3",
#     "Inv4227_eecc_R10_0_I3_w2Action"
#   ],
#   [
#     "Inv140_f68c_R9_0_I1",
#     "Inv4227_eecc_R10_0_I3_w2Action"
#   ],
H_Inv4227_eecc_R10_0_I3.children = {
    "w2Action": [H_Inv140_f68c_R9_0_I1, H_Inv80_b6ff_R2_0_I3, H_Inv11_3838_R8_0_I2],
    "e3bAction": [H_Inv2740_e784_R16_0_I3]
}

#   [
#     "Inv3293_1a1e_R17_0_I3",
#     "Inv32498_2818_R11_0_I2_e2bAction"
#   ],
#   [
#     "Inv2740_e784_R16_0_I3",
#     "Inv32498_2818_R11_0_I2_w1bAction"
#   ],
H_Inv32498_2818_R11_0_I2.children = {
    "w1bAction": [H_Inv2740_e784_R16_0_I3],
    "e2bAction": [H_Inv3293_1a1e_R17_0_I3]
}



#   [
#     "Inv0_b3ba_R18_0_I0",
#     "Inv2740_e784_R16_0_I3_e2bAction"
#   ],
#   [
#     "Inv6093_1c74_R18_1_I2",
#     "Inv2740_e784_R16_0_I3_w2Action"
#   ],
H_Inv2740_e784_R16_0_I3.children = {
    "e2bAction": [H_Inv0_b3ba_R18_0_I0],
    "w2Action": [H_Inv6093_1c74_R18_1_I2]
}






#   [
#     "Inv19_037d_R19_0_I1",
#     "Inv3293_1a1e_R17_0_I3_w1bAction"
#   ],

H_Inv3293_1a1e_R17_0_I3.children = {
    "w1bAction": [ H_Inv19_037d_R19_0_I1]
}


#   [
#     "Inv1_b58a_R20_0_I1",
#     "Inv0_b3ba_R18_0_I0_e2aAction"
#   ],
#   [
#     "Inv350_b077_R20_1_I2",
#     "Inv0_b3ba_R18_0_I0_w2Action"
#   ],
H_Inv0_b3ba_R18_0_I0.children = {
    "e2aAction": [H_Inv1_b58a_R20_0_I1],
    "w2Action": [H_Inv350_b077_R20_1_I2]
}


#   [
#     "Inv350_b077_R20_1_I2",
#     "Inv6093_1c74_R18_1_I2_e2bAction"
#   ],
#   [
#     "Inv103_c9b1_R21_1_I1",
#     "Inv6093_1c74_R18_1_I2_w1aAction"
#   ],
H_Inv6093_1c74_R18_1_I2.children = {
    "e2bAction": [H_Inv350_b077_R20_1_I2],
    "w1aAction": [H_Inv103_c9b1_R21_1_I1]
}
#   [
#     "Inv350_b077_R20_1_I2",
#     "Inv19_037d_R19_0_I1_w2Action"
#   ],
#   [
#     "Inv1_b58a_R20_0_I1",
#     "Inv19_037d_R19_0_I1_w2Action"
#   ],
H_Inv19_037d_R19_0_I1.children = {
    "w2Action": [H_Inv1_b58a_R20_0_I1, H_Inv350_b077_R20_1_I2]
}



#   [
#     "Inv350_b077_R20_1_I2",
#     "Inv1_b58a_R20_0_I1_w2Action"
#   ],
H_Inv1_b58a_R20_0_I1.children = {
    "w2Action": [H_Inv350_b077_R20_1_I2]
}


#   [
#     "Inv40_180c_R24_0_I1",
#     "Inv350_b077_R20_1_I2_w1aAction"
#   ],
H_Inv350_b077_R20_1_I2.children = {
    "w1aAction": [H_Inv40_180c_R24_0_I1]
}



#   [
#     "Inv40_180c_R24_0_I1",
#     "Inv103_c9b1_R21_1_I1_e2bAction"
#   ]
H_Inv103_c9b1_R21_1_I1.children = {
    "e2bAction": [H_Inv40_180c_R24_0_I1]
}

root = make_node("H_MutualExclusion")


#   [
#     "Inv4690_2f61_R0_0_I2",
#     "Safety_w1bAction"
#   ],
root.children = {
    "w1bAction": [H_Inv4690_2f61_R0_0_I2],
}










nodes = [
    # uniqueLeaders,
    # decidedImpliesLeader,
    # leaderImpliesVotesInQuorum,
    # nodesCantVoteTwice,
    # # voteRecordedImpliesNodeVoted,
    # nodesCantSendVotesToDifferentNodes,
    # voteMsgImpliesNodeVoted,
    # voteRecordedImpliesVoteMsg
]
actions = [
    "SendRequestVoteAction",
    "SendVoteAction",
    "RecvVoteAction",
    "BecomeLeaderAction",
    "DecideAction"
]