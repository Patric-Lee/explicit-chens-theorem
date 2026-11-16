import PlattAssemblyKernel
import PlattCertificates.Count131072.C049152
import PlattCertificates.Count131072.C049153
import PlattCertificates.Count131072.C049154
import PlattCertificates.Count131072.C049155
import PlattCertificates.Count131072.C049156
import PlattCertificates.Count131072.C049157
import PlattCertificates.Count131072.C049158
import PlattCertificates.Count131072.C049159
import PlattCertificates.Count131072.C049160
import PlattCertificates.Count131072.C049161
import PlattCertificates.Count131072.C049162
import PlattCertificates.Count131072.C049163
import PlattCertificates.Count131072.C049164
import PlattCertificates.Count131072.C049165
import PlattCertificates.Count131072.C049166
import PlattCertificates.Count131072.C049167
import PlattCertificates.Count131072.C049168
import PlattCertificates.Count131072.C049169
import PlattCertificates.Count131072.C049170
import PlattCertificates.Count131072.C049171
import PlattCertificates.Count131072.C049172
import PlattCertificates.Count131072.C049173
import PlattCertificates.Count131072.C049174
import PlattCertificates.Count131072.C049175
import PlattCertificates.Count131072.C049176
import PlattCertificates.Count131072.C049177
import PlattCertificates.Count131072.C049178
import PlattCertificates.Count131072.C049179
import PlattCertificates.Count131072.C049180
import PlattCertificates.Count131072.C049181
import PlattCertificates.Count131072.C049182
import PlattCertificates.Count131072.C049183
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000286
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49152 : List PrefixCut := [⟨64,253073980,253074122⟩]
theorem checked49152 : checkPrefixCuts (2^48) 6446383105 10 Manual.Count131072.C049152.packed 64 cuts49152 = true := by
 decide +kernel
def cuts49153 : List PrefixCut := [⟨8,30345827,30345845⟩,
⟨64,256343529,256343676⟩]
theorem checked49153 : checkPrefixCuts (2^48) 6446514177 10 Manual.Count131072.C049153.packed 64 cuts49153 = true := by
 decide +kernel
def pointBounds49153 : List (Nat × Nat × Nat) := [(6446530560,111444145402354,111444532403192)]
theorem point_links_checked49153 : (cuts49153.take 1).map (fun c => (6446514177-1+2*2^10*c.k,111444115056527+c.lower,111444502057347+c.upper)) = pointBounds49153 := by
 decide +kernel
def cuts49154 : List PrefixCut := [⟨43,170936459,170936561⟩,
⟨64,254897499,254897650⟩]
theorem checked49154 : checkPrefixCuts (2^48) 6446645249 10 Manual.Count131072.C049154.packed 64 cuts49154 = true := by
 decide +kernel
def pointBounds49154 : List (Nat × Nat × Nat) := [(6446733312,111444542336515,111444929337584)]
theorem point_links_checked49154 : (cuts49154.take 1).map (fun c => (6446645249-1+2*2^10*c.k,111444371400056+c.lower,111444758401023+c.upper)) = pointBounds49154 := by
 decide +kernel
def cuts49155 : List PrefixCut := [⟨64,254630340,254630481⟩]
theorem checked49155 : checkPrefixCuts (2^48) 6446776321 10 Manual.Count131072.C049155.packed 64 cuts49155 = true := by
 decide +kernel
def cuts49156 : List PrefixCut := [⟨14,54531782,54531812⟩,
⟨64,251045063,251045210⟩]
theorem checked49156 : checkPrefixCuts (2^48) 6446907393 10 Manual.Count131072.C049156.packed 64 cuts49156 = true := by
 decide +kernel
def pointBounds49156 : List (Nat × Nat × Nat) := [(6446936064,111444935459677,111445322460966)]
theorem point_links_checked49156 : (cuts49156.take 1).map (fun c => (6446907393-1+2*2^10*c.k,111444880927895+c.lower,111445267929154+c.upper)) = pointBounds49156 := by
 decide +kernel
def cuts49157 : List PrefixCut := [⟨49,194589163,194589270⟩,
⟨64,254794625,254794765⟩]
theorem checked49157 : checkPrefixCuts (2^48) 6447038465 10 Manual.Count131072.C049157.packed 64 cuts49157 = true := by
 decide +kernel
def pointBounds49157 : List (Nat × Nat × Nat) := [(6447138816,111445326562121,111445713563634)]
theorem point_links_checked49157 : (cuts49157.take 1).map (fun c => (6447038465-1+2*2^10*c.k,111445131972958+c.lower,111445518974364+c.upper)) = pointBounds49157 := by
 decide +kernel
def cuts49158 : List PrefixCut := [⟨64,253392398,253392542⟩]
theorem checked49158 : checkPrefixCuts (2^48) 6447169537 10 Manual.Count131072.C049158.packed 64 cuts49158 = true := by
 decide +kernel
def cuts49159 : List PrefixCut := [⟨20,78976692,78976736⟩,
⟨64,253649183,253649330⟩]
theorem checked49159 : checkPrefixCuts (2^48) 6447300609 10 Manual.Count131072.C049159.packed 64 cuts49159 = true := by
 decide +kernel
def pointBounds49159 : List (Nat × Nat × Nat) := [(6447341568,111445719136673,111446106138407)]
theorem point_links_checked49159 : (cuts49159.take 1).map (fun c => (6447300609-1+2*2^10*c.k,111445640159981+c.lower,111446027161671+c.upper)) = pointBounds49159 := by
 decide +kernel
def cuts49160 : List PrefixCut := [⟨55,220421765,220421889⟩,
⟨64,254386194,254386338⟩]
theorem checked49160 : checkPrefixCuts (2^48) 6447431681 10 Manual.Count131072.C049160.packed 64 cuts49160 = true := by
 decide +kernel
def pointBounds49160 : List (Nat × Nat × Nat) := [(6447544320,111446114230929,111446501232890)]
theorem point_links_checked49160 : (cuts49160.take 1).map (fun c => (6447431681-1+2*2^10*c.k,111445893809164+c.lower,111446280811001+c.upper)) = pointBounds49160 := by
 decide +kernel
def cuts49161 : List PrefixCut := [⟨64,256258178,256258321⟩]
theorem checked49161 : checkPrefixCuts (2^48) 6447562753 10 Manual.Count131072.C049161.packed 64 cuts49161 = true := by
 decide +kernel
def cuts49162 : List PrefixCut := [⟨26,103287606,103287665⟩,
⟨64,253022557,253022702⟩]
theorem checked49162 : checkPrefixCuts (2^48) 6447693825 10 Manual.Count131072.C049162.packed 64 cuts49162 = true := by
 decide +kernel
def pointBounds49162 : List (Nat × Nat × Nat) := [(6447747072,111446507741142,111446894743325)]
theorem point_links_checked49162 : (cuts49162.take 1).map (fun c => (6447693825-1+2*2^10*c.k,111446404453536+c.lower,111446791455660+c.upper)) = pointBounds49162 := by
 decide +kernel
def cuts49163 : List PrefixCut := [⟨61,239615779,239615919⟩,
⟨64,251052963,251053110⟩]
theorem checked49163 : checkPrefixCuts (2^48) 6447824897 10 Manual.Count131072.C049163.packed 64 cuts49163 = true := by
 decide +kernel
def pointBounds49163 : List (Nat × Nat × Nat) := [(6447949824,111446897091872,111447284094281)]
theorem point_links_checked49163 : (cuts49163.take 1).map (fun c => (6447824897-1+2*2^10*c.k,111446657476093+c.lower,111447044478362+c.upper)) = pointBounds49163 := by
 decide +kernel
def cuts49164 : List PrefixCut := [⟨64,247599292,247599436⟩]
theorem checked49164 : checkPrefixCuts (2^48) 6447955969 10 Manual.Count131072.C049164.packed 64 cuts49164 = true := by
 decide +kernel
def cuts49165 : List PrefixCut := [⟨32,129690822,129690892⟩,
⟨64,255364344,255364489⟩]
theorem checked49165 : checkPrefixCuts (2^48) 6448087041 10 Manual.Count131072.C049165.packed 64 cuts49165 = true := by
 decide +kernel
def pointBounds49165 : List (Nat × Nat × Nat) := [(6448152576,111447285819170,111447672821800)]
theorem point_links_checked49165 : (cuts49165.take 1).map (fun c => (6448087041-1+2*2^10*c.k,111447156128348+c.lower,111447543130908+c.upper)) = pointBounds49165 := by
 decide +kernel
def cuts49166 : List PrefixCut := [⟨64,251910670,251910816⟩]
theorem checked49166 : checkPrefixCuts (2^48) 6448218113 10 Manual.Count131072.C049166.packed 64 cuts49166 = true := by
 decide +kernel
def cuts49167 : List PrefixCut := [⟨3,11611079,11611085⟩,
⟨64,250639756,250639894⟩]
theorem checked49167 : checkPrefixCuts (2^48) 6448349185 10 Manual.Count131072.C049167.packed 64 cuts49167 = true := by
 decide +kernel
def pointBounds49167 : List (Nat × Nat × Nat) := [(6448355328,111447675014441,111448062017298)]
theorem point_links_checked49167 : (cuts49167.take 1).map (fun c => (6448349185-1+2*2^10*c.k,111447663403362+c.lower,111448050406213+c.upper)) = pointBounds49167 := by
 decide +kernel
def cuts49168 : List PrefixCut := [⟨38,148713994,148714078⟩,
⟨64,252205996,252206143⟩]
theorem checked49168 : checkPrefixCuts (2^48) 6448480257 10 Manual.Count131072.C049168.packed 64 cuts49168 = true := by
 decide +kernel
def pointBounds49168 : List (Nat × Nat × Nat) := [(6448558080,111448062757112,111448449760185)]
theorem point_links_checked49168 : (cuts49168.take 1).map (fun c => (6448480257-1+2*2^10*c.k,111447914043118+c.lower,111448301046107+c.upper)) = pointBounds49168 := by
 decide +kernel
def cuts49169 : List PrefixCut := [⟨64,254034118,254034260⟩]
theorem checked49169 : checkPrefixCuts (2^48) 6448611329 10 Manual.Count131072.C049169.packed 64 cuts49169 = true := by
 decide +kernel
def cuts49170 : List PrefixCut := [⟨9,35747686,35747706⟩,
⟨64,253243303,253243443⟩]
theorem checked49170 : checkPrefixCuts (2^48) 6448742401 10 Manual.Count131072.C049170.packed 64 cuts49170 = true := by
 decide +kernel
def pointBounds49170 : List (Nat × Nat × Nat) := [(6448760832,111448456030918,111448843034216)]
theorem point_links_checked49170 : (cuts49170.take 1).map (fun c => (6448742401-1+2*2^10*c.k,111448420283232+c.lower,111448807286510+c.upper)) = pointBounds49170 := by
 decide +kernel
def cuts49171 : List PrefixCut := [⟨44,176289584,176289683⟩,
⟨64,255769668,255769811⟩]
theorem checked49171 : checkPrefixCuts (2^48) 6448873473 10 Manual.Count131072.C049171.packed 64 cuts49171 = true := by
 decide +kernel
def pointBounds49171 : List (Nat × Nat × Nat) := [(6448963584,111448849816119,111449236819636)]
theorem point_links_checked49171 : (cuts49171.take 1).map (fun c => (6448873473-1+2*2^10*c.k,111448673526535+c.lower,111449060529953+c.upper)) = pointBounds49171 := by
 decide +kernel
def cuts49172 : List PrefixCut := [⟨64,255371649,255371792⟩]
theorem checked49172 : checkPrefixCuts (2^48) 6449004545 10 Manual.Count131072.C049172.packed 64 cuts49172 = true := by
 decide +kernel
def cuts49173 : List PrefixCut := [⟨15,60405047,60405079⟩,
⟨64,255671970,255672116⟩]
theorem checked49173 : checkPrefixCuts (2^48) 6449135617 10 Manual.Count131072.C049173.packed 64 cuts49173 = true := by
 decide +kernel
def pointBounds49173 : List (Nat × Nat × Nat) := [(6449166336,111449245072899,111449632076635)]
theorem point_links_checked49173 : (cuts49173.take 1).map (fun c => (6449135617-1+2*2^10*c.k,111449184667852+c.lower,111449571671556+c.upper)) = pointBounds49173 := by
 decide +kernel
def cuts49174 : List PrefixCut := [⟨50,200370233,200370351⟩,
⟨64,256845168,256845320⟩]
theorem checked49174 : checkPrefixCuts (2^48) 6449266689 10 Manual.Count131072.C049174.packed 64 cuts49174 = true := by
 decide +kernel
def pointBounds49174 : List (Nat × Nat × Nat) := [(6449369088,111449640710055,111450027714023)]
theorem point_links_checked49174 : (cuts49174.take 1).map (fun c => (6449266689-1+2*2^10*c.k,111449440339822+c.lower,111449827343672+c.upper)) = pointBounds49174 := by
 decide +kernel
def cuts49175 : List PrefixCut := [⟨64,255050576,255050719⟩]
theorem checked49175 : checkPrefixCuts (2^48) 6449397761 10 Manual.Count131072.C049175.packed 64 cuts49175 = true := by
 decide +kernel
def cuts49176 : List PrefixCut := [⟨21,81437022,81437067⟩,
⟨64,252252270,252252410⟩]
theorem checked49176 : checkPrefixCuts (2^48) 6449528833 10 Manual.Count131072.C049176.packed 64 cuts49176 = true := by
 decide +kernel
def pointBounds49176 : List (Nat × Nat × Nat) := [(6449571840,111450033672588,111450420676778)]
theorem point_links_checked49176 : (cuts49176.take 1).map (fun c => (6449528833-1+2*2^10*c.k,111449952235566+c.lower,111450339239711+c.upper)) = pointBounds49176 := by
 decide +kernel
def cuts49177 : List PrefixCut := [⟨56,221480270,221480395⟩,
⟨64,252639936,252640078⟩]
theorem checked49177 : checkPrefixCuts (2^48) 6449659905 10 Manual.Count131072.C049177.packed 64 cuts49177 = true := by
 decide +kernel
def pointBounds49177 : List (Nat × Nat × Nat) := [(6449774592,111450425968106,111450812972516)]
theorem point_links_checked49177 : (cuts49177.take 1).map (fun c => (6449659905-1+2*2^10*c.k,111450204487836+c.lower,111450591492121+c.upper)) = pointBounds49177 := by
 decide +kernel
def cuts49178 : List PrefixCut := [⟨64,251412872,251413014⟩]
theorem checked49178 : checkPrefixCuts (2^48) 6449790977 10 Manual.Count131072.C049178.packed 64 cuts49178 = true := by
 decide +kernel
def cuts49179 : List PrefixCut := [⟨27,103862872,103862930⟩,
⟨64,251145895,251146036⟩]
theorem checked49179 : checkPrefixCuts (2^48) 6449922049 10 Manual.Count131072.C049179.packed 64 cuts49179 = true := by
 decide +kernel
def pointBounds49179 : List (Nat × Nat × Nat) := [(6449977344,111450812403516,111451199408143)]
theorem point_links_checked49179 : (cuts49179.take 1).map (fun c => (6449922049-1+2*2^10*c.k,111450708540644+c.lower,111451095545213+c.upper)) = pointBounds49179 := by
 decide +kernel
def cuts49180 : List PrefixCut := [⟨62,245206013,245206153⟩,
⟨64,253148181,253148325⟩]
theorem checked49180 : checkPrefixCuts (2^48) 6450053121 10 Manual.Count131072.C049180.packed 64 cuts49180 = true := by
 decide +kernel
def pointBounds49180 : List (Nat × Nat × Nat) := [(6450180096,111451204892552,111451591897402)]
theorem point_links_checked49180 : (cuts49180.take 1).map (fun c => (6450053121-1+2*2^10*c.k,111450959686539+c.lower,111451346691249+c.upper)) = pointBounds49180 := by
 decide +kernel
def cuts49181 : List PrefixCut := [⟨64,254670375,254670527⟩]
theorem checked49181 : checkPrefixCuts (2^48) 6450184193 10 Manual.Count131072.C049181.packed 64 cuts49181 = true := by
 decide +kernel
def cuts49182 : List PrefixCut := [⟨33,130649645,130649720⟩,
⟨64,253181547,253181690⟩]
theorem checked49182 : checkPrefixCuts (2^48) 6450315265 10 Manual.Count131072.C049182.packed 64 cuts49182 = true := by
 decide +kernel
def pointBounds49182 : List (Nat × Nat × Nat) := [(6450382848,111451598154740,111451985159821)]
theorem point_links_checked49182 : (cuts49182.take 1).map (fun c => (6450315265-1+2*2^10*c.k,111451467505095+c.lower,111451854510101+c.upper)) = pointBounds49182 := by
 decide +kernel
def cuts49183 : List PrefixCut := [⟨64,253394589,253394733⟩]
theorem checked49183 : checkPrefixCuts (2^48) 6450446337 10 Manual.Count131072.C049183.packed 64 cuts49183 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000286
