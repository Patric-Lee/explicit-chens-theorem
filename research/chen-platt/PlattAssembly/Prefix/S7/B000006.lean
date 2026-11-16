import PlattAssemblyKernel
import PlattCertificates.Count131072.C060192
import PlattCertificates.Count131072.C060193
import PlattCertificates.Count131072.C060194
import PlattCertificates.Count131072.C060195
import PlattCertificates.Count131072.C060196
import PlattCertificates.Count131072.C060197
import PlattCertificates.Count131072.C060198
import PlattCertificates.Count131072.C060199
import PlattCertificates.Count131072.C060200
import PlattCertificates.Count131072.C060201
import PlattCertificates.Count131072.C060202
import PlattCertificates.Count131072.C060203
import PlattCertificates.Count131072.C060204
import PlattCertificates.Count131072.C060205
import PlattCertificates.Count131072.C060206
import PlattCertificates.Count131072.C060207
import PlattCertificates.Count131072.C060208
import PlattCertificates.Count131072.C060209
import PlattCertificates.Count131072.C060210
import PlattCertificates.Count131072.C060211
import PlattCertificates.Count131072.C060212
import PlattCertificates.Count131072.C060213
import PlattCertificates.Count131072.C060214
import PlattCertificates.Count131072.C060215
import PlattCertificates.Count131072.C060216
import PlattCertificates.Count131072.C060217
import PlattCertificates.Count131072.C060218
import PlattCertificates.Count131072.C060219
import PlattCertificates.Count131072.C060220
import PlattCertificates.Count131072.C060221
import PlattCertificates.Count131072.C060222
import PlattCertificates.Count131072.C060223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60192 : List PrefixCut := [⟨64,207286624,207286743⟩]
theorem checked60192 : checkPrefixCuts (2^48) 7893417985 10 Manual.Count131072.C060192.packed 64 cuts60192 = true := by
 decide +kernel
def cuts60193 : List PrefixCut := [⟨45,142527592,142527677⟩,
⟨64,205107991,205108112⟩]
theorem checked60193 : checkPrefixCuts (2^48) 7893549057 10 Manual.Count131072.C060193.packed 64 cuts60193 = true := by
 decide +kernel
def pointBounds60193 : List (Nat × Nat × Nat) := [(7893641216,113956576087078,113956964517044)]
theorem point_links_checked60193 : (cuts60193.take 1).map (fun c => (7893549057-1+2*2^10*c.k,113956433559486+c.lower,113956821989367+c.upper)) = pointBounds60193 := by
 decide +kernel
def cuts60194 : List PrefixCut := [⟨64,205211569,205211682⟩]
theorem checked60194 : checkPrefixCuts (2^48) 7893680129 10 Manual.Count131072.C060194.packed 64 cuts60194 = true := by
 decide +kernel
def cuts60195 : List PrefixCut := [⟨38,122019938,122020011⟩,
⟨64,205814347,205814469⟩]
theorem checked60195 : checkPrefixCuts (2^48) 7893811201 10 Manual.Count131072.C060195.packed 64 cuts60195 = true := by
 decide +kernel
def pointBounds60195 : List (Nat × Nat × Nat) := [(7893889024,113956965898984,113957354329172)]
theorem point_links_checked60195 : (cuts60195.take 1).map (fun c => (7893811201-1+2*2^10*c.k,113956843879046+c.lower,113957232309161+c.upper)) = pointBounds60195 := by
 decide +kernel
def cuts60196 : List PrefixCut := [⟨64,201353827,201353945⟩]
theorem checked60196 : checkPrefixCuts (2^48) 7893942273 10 Manual.Count131072.C060196.packed 64 cuts60196 = true := by
 decide +kernel
def cuts60197 : List PrefixCut := [⟨31,100372598,100372653⟩,
⟨64,203989059,203989172⟩]
theorem checked60197 : checkPrefixCuts (2^48) 7894073345 10 Manual.Count131072.C060197.packed 64 cuts60197 = true := by
 decide +kernel
def pointBounds60197 : List (Nat × Nat × Nat) := [(7894136832,113957351419818,113957739850228)]
theorem point_links_checked60197 : (cuts60197.take 1).map (fun c => (7894073345-1+2*2^10*c.k,113957251047220+c.lower,113957639477575+c.upper)) = pointBounds60197 := by
 decide +kernel
def cuts60198 : List PrefixCut := [⟨64,205590164,205590280⟩]
theorem checked60198 : checkPrefixCuts (2^48) 7894204417 10 Manual.Count131072.C060198.packed 64 cuts60198 = true := by
 decide +kernel
def cuts60199 : List PrefixCut := [⟨24,77264796,77264840⟩,
⟨64,205729378,205729493⟩]
theorem checked60199 : checkPrefixCuts (2^48) 7894335489 10 Manual.Count131072.C060199.packed 64 cuts60199 = true := by
 decide +kernel
def pointBounds60199 : List (Nat × Nat × Nat) := [(7894384640,113957737891239,113958126321867)]
theorem point_links_checked60199 : (cuts60199.take 1).map (fun c => (7894335489-1+2*2^10*c.k,113957660626443+c.lower,113958049057027+c.upper)) = pointBounds60199 := by
 decide +kernel
def cuts60200 : List PrefixCut := [⟨64,204299790,204299909⟩]
theorem checked60200 : checkPrefixCuts (2^48) 7894466561 10 Manual.Count131072.C060200.packed 64 cuts60200 = true := by
 decide +kernel
def cuts60201 : List PrefixCut := [⟨17,54871562,54871590⟩,
⟨64,203012857,203012971⟩]
theorem checked60201 : checkPrefixCuts (2^48) 7894597633 10 Manual.Count131072.C060201.packed 64 cuts60201 = true := by
 decide +kernel
def pointBounds60201 : List (Nat × Nat × Nat) := [(7894632448,113958125527173,113958513958019)]
theorem point_links_checked60201 : (cuts60201.take 1).map (fun c => (7894597633-1+2*2^10*c.k,113958070655611+c.lower,113958459086429+c.upper)) = pointBounds60201 := by
 decide +kernel
def cuts60202 : List PrefixCut := [⟨64,200585030,200585149⟩]
theorem checked60202 : checkPrefixCuts (2^48) 7894728705 10 Manual.Count131072.C060202.packed 64 cuts60202 = true := by
 decide +kernel
def cuts60203 : List PrefixCut := [⟨10,30518869,30518887⟩,
⟨64,206036576,206036691⟩]
theorem checked60203 : checkPrefixCuts (2^48) 7894859777 10 Manual.Count131072.C060203.packed 64 cuts60203 = true := by
 decide +kernel
def pointBounds60203 : List (Nat × Nat × Nat) := [(7894880256,113958504772367,113958893203436)]
theorem point_links_checked60203 : (cuts60203.take 1).map (fun c => (7894859777-1+2*2^10*c.k,113958474253498+c.lower,113958862684549+c.upper)) = pointBounds60203 := by
 decide +kernel
def cuts60204 : List PrefixCut := [⟨64,205177516,205177631⟩]
theorem checked60204 : checkPrefixCuts (2^48) 7894990849 10 Manual.Count131072.C060204.packed 64 cuts60204 = true := by
 decide +kernel
def cuts60205 : List PrefixCut := [⟨3,9519014,9519018⟩,
⟨64,203355883,203355995⟩]
theorem checked60205 : checkPrefixCuts (2^48) 7895121921 10 Manual.Count131072.C060205.packed 64 cuts60205 = true := by
 decide +kernel
def pointBounds60205 : List (Nat × Nat × Nat) := [(7895128064,113958894986604,113959283417889)]
theorem point_links_checked60205 : (cuts60205.take 1).map (fun c => (7895121921-1+2*2^10*c.k,113958885467590+c.lower,113959273898871+c.upper)) = pointBounds60205 := by
 decide +kernel
def cuts60206 : List PrefixCut := [⟨60,194903346,194903457⟩,
⟨64,207523653,207523772⟩]
theorem checked60206 : checkPrefixCuts (2^48) 7895252993 10 Manual.Count131072.C060206.packed 64 cuts60206 = true := by
 decide +kernel
def pointBounds60206 : List (Nat × Nat × Nat) := [(7895375872,113959283726819,113959672158323)]
theorem point_links_checked60206 : (cuts60206.take 1).map (fun c => (7895252993-1+2*2^10*c.k,113959088823473+c.lower,113959477254866+c.upper)) = pointBounds60206 := by
 decide +kernel
def cuts60207 : List PrefixCut := [⟨64,206486351,206486470⟩]
theorem checked60207 : checkPrefixCuts (2^48) 7895384065 10 Manual.Count131072.C060207.packed 64 cuts60207 = true := by
 decide +kernel
def cuts60208 : List PrefixCut := [⟨53,170690891,170690987⟩,
⟨64,207267209,207267325⟩]
theorem checked60208 : checkPrefixCuts (2^48) 7895515137 10 Manual.Count131072.C060208.packed 64 cuts60208 = true := by
 decide +kernel
def pointBounds60208 : List (Nat × Nat × Nat) := [(7895623680,113959673524368,113960061956095)]
theorem point_links_checked60208 : (cuts60208.take 1).map (fun c => (7895515137-1+2*2^10*c.k,113959502833477+c.lower,113959891265108+c.upper)) = pointBounds60208 := by
 decide +kernel
def cuts60209 : List PrefixCut := [⟨64,203663219,203663336⟩]
theorem checked60209 : checkPrefixCuts (2^48) 7895646209 10 Manual.Count131072.C060209.packed 64 cuts60209 = true := by
 decide +kernel
def cuts60210 : List PrefixCut := [⟨46,146943433,146943520⟩,
⟨64,203624197,203624315⟩]
theorem checked60210 : checkPrefixCuts (2^48) 7895777281 10 Manual.Count131072.C060210.packed 64 cuts60210 = true := by
 decide +kernel
def pointBounds60210 : List (Nat × Nat × Nat) := [(7895871488,113960060707338,113960449139289)]
theorem point_links_checked60210 : (cuts60210.take 1).map (fun c => (7895777281-1+2*2^10*c.k,113959913763905+c.lower,113960302195769+c.upper)) = pointBounds60210 := by
 decide +kernel
def cuts60211 : List PrefixCut := [⟨64,206009219,206009336⟩]
theorem checked60211 : checkPrefixCuts (2^48) 7895908353 10 Manual.Count131072.C060211.packed 64 cuts60211 = true := by
 decide +kernel
def cuts60212 : List PrefixCut := [⟨39,124302571,124302641⟩,
⟨64,203688728,203688843⟩]
theorem checked60212 : checkPrefixCuts (2^48) 7896039425 10 Manual.Count131072.C060212.packed 64 cuts60212 = true := by
 decide +kernel
def pointBounds60212 : List (Nat × Nat × Nat) := [(7896119296,113960447699892,113960836132061)]
theorem point_links_checked60212 : (cuts60212.take 1).map (fun c => (7896039425-1+2*2^10*c.k,113960323397321+c.lower,113960711829420+c.upper)) = pointBounds60212 := by
 decide +kernel
def cuts60213 : List PrefixCut := [⟨64,201011845,201011960⟩]
theorem checked60213 : checkPrefixCuts (2^48) 7896170497 10 Manual.Count131072.C060213.packed 64 cuts60213 = true := by
 decide +kernel
def cuts60214 : List PrefixCut := [⟨32,104015827,104015887⟩,
⟨64,204287966,204288081⟩]
theorem checked60214 : checkPrefixCuts (2^48) 7896301569 10 Manual.Count131072.C060214.packed 64 cuts60214 = true := by
 decide +kernel
def pointBounds60214 : List (Nat × Nat × Nat) := [(7896367104,113960832113721,113961220546110)]
theorem point_links_checked60214 : (cuts60214.take 1).map (fun c => (7896301569-1+2*2^10*c.k,113960728097894+c.lower,113961116530223+c.upper)) = pointBounds60214 := by
 decide +kernel
def cuts60215 : List PrefixCut := [⟨64,205781668,205781781⟩]
theorem checked60215 : checkPrefixCuts (2^48) 7896432641 10 Manual.Count131072.C060215.packed 64 cuts60215 = true := by
 decide +kernel
def cuts60216 : List PrefixCut := [⟨25,79845071,79845119⟩,
⟨64,204245530,204245647⟩]
theorem checked60216 : checkPrefixCuts (2^48) 7896563713 10 Manual.Count131072.C060216.packed 64 cuts60216 = true := by
 decide +kernel
def pointBounds60216 : List (Nat × Nat × Nat) := [(7896614912,113961218012599,113961606445204)]
theorem point_links_checked60216 : (cuts60216.take 1).map (fun c => (7896563713-1+2*2^10*c.k,113961138167528+c.lower,113961526600085+c.upper)) = pointBounds60216 := by
 decide +kernel
def cuts60217 : List PrefixCut := [⟨64,205667912,205668025⟩]
theorem checked60217 : checkPrefixCuts (2^48) 7896694785 10 Manual.Count131072.C060217.packed 64 cuts60217 = true := by
 decide +kernel
def cuts60218 : List PrefixCut := [⟨18,58848197,58848230⟩,
⟨64,207411045,207411165⟩]
theorem checked60218 : checkPrefixCuts (2^48) 7896825857 10 Manual.Count131072.C060218.packed 64 cuts60218 = true := by
 decide +kernel
def pointBounds60218 : List (Nat × Nat × Nat) := [(7896862720,113961606929167,113961995361987)]
theorem point_links_checked60218 : (cuts60218.take 1).map (fun c => (7896825857-1+2*2^10*c.k,113961548080970+c.lower,113961936513757+c.upper)) = pointBounds60218 := by
 decide +kernel
def cuts60219 : List PrefixCut := [⟨64,203843279,203843391⟩]
theorem checked60219 : checkPrefixCuts (2^48) 7896956929 10 Manual.Count131072.C060219.packed 64 cuts60219 = true := by
 decide +kernel
def cuts60220 : List PrefixCut := [⟨11,35535894,35535912⟩,
⟨64,205123029,205123140⟩]
theorem checked60220 : checkPrefixCuts (2^48) 7897088001 10 Manual.Count131072.C060220.packed 64 cuts60220 = true := by
 decide +kernel
def pointBounds60220 : List (Nat × Nat × Nat) := [(7897110528,113961994871188,113962383304225)]
theorem point_links_checked60220 : (cuts60220.take 1).map (fun c => (7897088001-1+2*2^10*c.k,113961959335294+c.lower,113962347768313+c.upper)) = pointBounds60220 := by
 decide +kernel
def cuts60221 : List PrefixCut := [⟨64,207436346,207436467⟩]
theorem checked60221 : checkPrefixCuts (2^48) 7897219073 10 Manual.Count131072.C060221.packed 64 cuts60221 = true := by
 decide +kernel
def cuts60222 : List PrefixCut := [⟨4,13757685,13757693⟩,
⟨64,208003189,208003304⟩]
theorem checked60222 : checkPrefixCuts (2^48) 7897350145 10 Manual.Count131072.C060222.packed 64 cuts60222 = true := by
 decide +kernel
def pointBounds60222 : List (Nat × Nat × Nat) := [(7897358336,113962385652354,113962774085613)]
theorem point_links_checked60222 : (cuts60222.take 1).map (fun c => (7897350145-1+2*2^10*c.k,113962371894669+c.lower,113962760327920+c.upper)) = pointBounds60222 := by
 decide +kernel
def cuts60223 : List PrefixCut := [⟨61,194171164,194171277⟩,
⟨64,204079228,204079347⟩]
theorem checked60223 : checkPrefixCuts (2^48) 7897481217 10 Manual.Count131072.C060223.packed 64 cuts60223 = true := by
 decide +kernel
def pointBounds60223 : List (Nat × Nat × Nat) := [(7897606144,113962774069022,113963162502501)]
theorem point_links_checked60223 : (cuts60223.take 1).map (fun c => (7897481217-1+2*2^10*c.k,113962579897858+c.lower,113962968331224+c.upper)) = pointBounds60223 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000006
