import PlattAssemblyKernel
import PlattCertificates.Count131072.C036176
import PlattCertificates.Count131072.C036177
import PlattCertificates.Count131072.C036178
import PlattCertificates.Count131072.C036179
import PlattCertificates.Count131072.C036180
import PlattCertificates.Count131072.C036181
import PlattCertificates.Count131072.C036182
import PlattCertificates.Count131072.C036183
import PlattCertificates.Count131072.C036184
import PlattCertificates.Count131072.C036185
import PlattCertificates.Count131072.C036186
import PlattCertificates.Count131072.C036187
import PlattCertificates.Count131072.C036188
import PlattCertificates.Count131072.C036189
import PlattCertificates.Count131072.C036190
import PlattCertificates.Count131072.C036191
import PlattCertificates.Count131072.C036192
import PlattCertificates.Count131072.C036193
import PlattCertificates.Count131072.C036194
import PlattCertificates.Count131072.C036195
import PlattCertificates.Count131072.C036196
import PlattCertificates.Count131072.C036197
import PlattCertificates.Count131072.C036198
import PlattCertificates.Count131072.C036199
import PlattCertificates.Count131072.C036200
import PlattCertificates.Count131072.C036201
import PlattCertificates.Count131072.C036202
import PlattCertificates.Count131072.C036203
import PlattCertificates.Count131072.C036204
import PlattCertificates.Count131072.C036205
import PlattCertificates.Count131072.C036206
import PlattCertificates.Count131072.C036207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000193
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36176 : List PrefixCut := [⟨64,350415774,350415992⟩]
theorem checked36176 : checkPrefixCuts (2^48) 4745592833 10 Manual.Count131072.C036176.packed 64 cuts36176 = true := by
 decide +kernel
def cuts36177 : List PrefixCut := [⟨5,27461086,27461104⟩,
⟨64,354142674,354142891⟩]
theorem checked36177 : checkPrefixCuts (2^48) 4745723905 10 Manual.Count131072.C036177.packed 64 cuts36177 = true := by
 decide +kernel
def pointBounds36177 : List (Nat × Nat × Nat) := [(4745734144,107601069145509,107601453886719)]
theorem point_links_checked36177 : (cuts36177.take 1).map (fun c => (4745723905-1+2*2^10*c.k,107601041684423+c.lower,107601426425615+c.upper)) = pointBounds36177 := by
 decide +kernel
def cuts36178 : List PrefixCut := [⟨14,76687118,76687165⟩,
⟨64,344702773,344702989⟩]
theorem checked36178 : checkPrefixCuts (2^48) 4745854977 10 Manual.Count131072.C036178.packed 64 cuts36178 = true := by
 decide +kernel
def pointBounds36178 : List (Nat × Nat × Nat) := [(4745883648,107601472514215,107601857255671)]
theorem point_links_checked36178 : (cuts36178.take 1).map (fun c => (4745854977-1+2*2^10*c.k,107601395827097+c.lower,107601780568506+c.upper)) = pointBounds36178 := by
 decide +kernel
def cuts36179 : List PrefixCut := [⟨23,124842688,124842765⟩,
⟨64,350564678,350564889⟩]
theorem checked36179 : checkPrefixCuts (2^48) 4745986049 10 Manual.Count131072.C036179.packed 64 cuts36179 = true := by
 decide +kernel
def pointBounds36179 : List (Nat × Nat × Nat) := [(4746033152,107601865372558,107602250114260)]
theorem point_links_checked36179 : (cuts36179.take 1).map (fun c => (4745986049-1+2*2^10*c.k,107601740529870+c.lower,107602125271495+c.upper)) = pointBounds36179 := by
 decide +kernel
def cuts36180 : List PrefixCut := [⟨32,174952533,174952639⟩,
⟨64,349190979,349191191⟩]
theorem checked36180 : checkPrefixCuts (2^48) 4746117121 10 Manual.Count131072.C036180.packed 64 cuts36180 = true := by
 decide +kernel
def pointBounds36180 : List (Nat × Nat × Nat) := [(4746182656,107602266047081,107602650789023)]
theorem point_links_checked36180 : (cuts36180.take 1).map (fun c => (4746117121-1+2*2^10*c.k,107602091094548+c.lower,107602475836384+c.upper)) = pointBounds36180 := by
 decide +kernel
def cuts36181 : List PrefixCut := [⟨41,224169845,224169983⟩,
⟨64,351375576,351375792⟩]
theorem checked36181 : checkPrefixCuts (2^48) 4746248193 10 Manual.Count131072.C036181.packed 64 cuts36181 = true := by
 decide +kernel
def pointBounds36181 : List (Nat × Nat × Nat) := [(4746332160,107602664455372,107603049197558)]
theorem point_links_checked36181 : (cuts36181.take 1).map (fun c => (4746248193-1+2*2^10*c.k,107602440285527+c.lower,107602825027575+c.upper)) = pointBounds36181 := by
 decide +kernel
def cuts36182 : List PrefixCut := [⟨50,274688910,274689082⟩,
⟨64,351484506,351484727⟩]
theorem checked36182 : checkPrefixCuts (2^48) 4746379265 10 Manual.Count131072.C036182.packed 64 cuts36182 = true := by
 decide +kernel
def pointBounds36182 : List (Nat × Nat × Nat) := [(4746481664,107603066350013,107603451092449)]
theorem point_links_checked36182 : (cuts36182.take 1).map (fun c => (4746379265-1+2*2^10*c.k,107602791661103+c.lower,107603176403367+c.upper)) = pointBounds36182 := by
 decide +kernel
def cuts36183 : List PrefixCut := [⟨59,322121289,322121487⟩,
⟨64,347501631,347501845⟩]
theorem checked36183 : checkPrefixCuts (2^48) 4746510337 10 Manual.Count131072.C036183.packed 64 cuts36183 = true := by
 decide +kernel
def pointBounds36183 : List (Nat × Nat × Nat) := [(4746631168,107603465266898,107603850009581)]
theorem point_links_checked36183 : (cuts36183.take 1).map (fun c => (4746510337-1+2*2^10*c.k,107603143145609+c.lower,107603527888094+c.upper)) = pointBounds36183 := by
 decide +kernel
def cuts36184 : List PrefixCut := [⟨64,347966415,347966629⟩]
theorem checked36184 : checkPrefixCuts (2^48) 4746641409 10 Manual.Count131072.C036184.packed 64 cuts36184 = true := by
 decide +kernel
def cuts36185 : List PrefixCut := [⟨4,22889072,22889086⟩,
⟨64,351396089,351396300⟩]
theorem checked36185 : checkPrefixCuts (2^48) 4746772481 10 Manual.Count131072.C036185.packed 64 cuts36185 = true := by
 decide +kernel
def pointBounds36185 : List (Nat × Nat × Nat) := [(4746780672,107603861502727,107604246245654)]
theorem point_links_checked36185 : (cuts36185.take 1).map (fun c => (4746772481-1+2*2^10*c.k,107603838613655+c.lower,107604223356568+c.upper)) = pointBounds36185 := by
 decide +kernel
def cuts36186 : List PrefixCut := [⟨13,69673223,69673268⟩,
⟨64,346049729,346049942⟩]
theorem checked36186 : checkPrefixCuts (2^48) 4746903553 10 Manual.Count131072.C036186.packed 64 cuts36186 = true := by
 decide +kernel
def pointBounds36186 : List (Nat × Nat × Nat) := [(4746930176,107604259682967,107604644426136)]
theorem point_links_checked36186 : (cuts36186.take 1).map (fun c => (4746903553-1+2*2^10*c.k,107604190009744+c.lower,107604574752868+c.upper)) = pointBounds36186 := by
 decide +kernel
def cuts36187 : List PrefixCut := [⟨22,118411333,118411404⟩,
⟨64,346811000,346811209⟩]
theorem checked36187 : checkPrefixCuts (2^48) 4747034625 10 Manual.Count131072.C036187.packed 64 cuts36187 = true := by
 decide +kernel
def pointBounds36187 : List (Nat × Nat × Nat) := [(4747079680,107604654470806,107605039214214)]
theorem point_links_checked36187 : (cuts36187.take 1).map (fun c => (4747034625-1+2*2^10*c.k,107604536059473+c.lower,107604920802810+c.upper)) = pointBounds36187 := by
 decide +kernel
def cuts36188 : List PrefixCut := [⟨31,166494328,166494434⟩,
⟨64,345081946,345082163⟩]
theorem checked36188 : checkPrefixCuts (2^48) 4747165697 10 Manual.Count131072.C036188.packed 64 cuts36188 = true := by
 decide +kernel
def pointBounds36188 : List (Nat × Nat × Nat) := [(4747229184,107605049364801,107605434108453)]
theorem point_links_checked36188 : (cuts36188.take 1).map (fun c => (4747165697-1+2*2^10*c.k,107604882870473+c.lower,107605267614019+c.upper)) = pointBounds36188 := by
 decide +kernel
def cuts36189 : List PrefixCut := [⟨40,221037220,221037361⟩,
⟨64,354618241,354618461⟩]
theorem checked36189 : checkPrefixCuts (2^48) 4747296769 10 Manual.Count131072.C036189.packed 64 cuts36189 = true := by
 decide +kernel
def pointBounds36189 : List (Nat × Nat × Nat) := [(4747378688,107605448989639,107605833733543)]
theorem point_links_checked36189 : (cuts36189.take 1).map (fun c => (4747296769-1+2*2^10*c.k,107605227952419+c.lower,107605612696182+c.upper)) = pointBounds36189 := by
 decide +kernel
def cuts36190 : List PrefixCut := [⟨49,268343607,268343777⟩,
⟨64,351584701,351584921⟩]
theorem checked36190 : checkPrefixCuts (2^48) 4747427841 10 Manual.Count131072.C036190.packed 64 cuts36190 = true := by
 decide +kernel
def pointBounds36190 : List (Nat × Nat × Nat) := [(4747528192,107605850914267,107606235658420)]
theorem point_links_checked36190 : (cuts36190.take 1).map (fun c => (4747427841-1+2*2^10*c.k,107605582570660+c.lower,107605967314643+c.upper)) = pointBounds36190 := by
 decide +kernel
def cuts36191 : List PrefixCut := [⟨58,314520704,314520900⟩,
⟨64,345705551,345705766⟩]
theorem checked36191 : checkPrefixCuts (2^48) 4747558913 10 Manual.Count131072.C036191.packed 64 cuts36191 = true := by
 decide +kernel
def pointBounds36191 : List (Nat × Nat × Nat) := [(4747677696,107606248676065,107606633420464)]
theorem point_links_checked36191 : (cuts36191.take 1).map (fun c => (4747558913-1+2*2^10*c.k,107605934155361+c.lower,107606318899564+c.upper)) = pointBounds36191 := by
 decide +kernel
def cuts36192 : List PrefixCut := [⟨64,359331776,359331993⟩]
theorem checked36192 : checkPrefixCuts (2^48) 4747689985 10 Manual.Count131072.C036192.packed 64 cuts36192 = true := by
 decide +kernel
def cuts36193 : List PrefixCut := [⟨3,16125527,16125537⟩,
⟨64,350014209,350014424⟩]
theorem checked36193 : checkPrefixCuts (2^48) 4747821057 10 Manual.Count131072.C036193.packed 64 cuts36193 = true := by
 decide +kernel
def pointBounds36193 : List (Nat × Nat × Nat) := [(4747827200,107606655318215,107607040062860)]
theorem point_links_checked36193 : (cuts36193.take 1).map (fun c => (4747821057-1+2*2^10*c.k,107606639192688+c.lower,107607023937323+c.upper)) = pointBounds36193 := by
 decide +kernel
def cuts36194 : List PrefixCut := [⟨12,64678054,64678095⟩,
⟨64,348403928,348404147⟩]
theorem checked36194 : checkPrefixCuts (2^48) 4747952129 10 Manual.Count131072.C036194.packed 64 cuts36194 = true := by
 decide +kernel
def pointBounds36194 : List (Nat × Nat × Nat) := [(4747976704,107607053884951,107607438629842)]
theorem point_links_checked36194 : (cuts36194.take 1).map (fun c => (4747952129-1+2*2^10*c.k,107606989206897+c.lower,107607373951747+c.upper)) = pointBounds36194 := by
 decide +kernel
def cuts36195 : List PrefixCut := [⟨21,114116944,114117013⟩,
⟨64,347564372,347564585⟩]
theorem checked36195 : checkPrefixCuts (2^48) 4748083201 10 Manual.Count131072.C036195.packed 64 cuts36195 = true := by
 decide +kernel
def pointBounds36195 : List (Nat × Nat × Nat) := [(4748126208,107607451727769,107607836472907)]
theorem point_links_checked36195 : (cuts36195.take 1).map (fun c => (4748083201-1+2*2^10*c.k,107607337610825+c.lower,107607722355894+c.upper)) = pointBounds36195 := by
 decide +kernel
def cuts36196 : List PrefixCut := [⟨30,163493627,163493726⟩,
⟨64,350933687,350933903⟩]
theorem checked36196 : checkPrefixCuts (2^48) 4748214273 10 Manual.Count131072.C036196.packed 64 cuts36196 = true := by
 decide +kernel
def pointBounds36196 : List (Nat × Nat × Nat) := [(4748275712,107607848668824,107608233414205)]
theorem point_links_checked36196 : (cuts36196.take 1).map (fun c => (4748214273-1+2*2^10*c.k,107607685175197+c.lower,107608069920479+c.upper)) = pointBounds36196 := by
 decide +kernel
def cuts36197 : List PrefixCut := [⟨39,213282319,213282453⟩,
⟨64,346418909,346419128⟩]
theorem checked36197 : checkPrefixCuts (2^48) 4748345345 10 Manual.Count131072.C036197.packed 64 cuts36197 = true := by
 decide +kernel
def pointBounds36197 : List (Nat × Nat × Nat) := [(4748425216,107608249391203,107608634136835)]
theorem point_links_checked36197 : (cuts36197.take 1).map (fun c => (4748345345-1+2*2^10*c.k,107608036108884+c.lower,107608420854382+c.upper)) = pointBounds36197 := by
 decide +kernel
def cuts36198 : List PrefixCut := [⟨48,267276734,267276899⟩,
⟨64,352396287,352396503⟩]
theorem checked36198 : checkPrefixCuts (2^48) 4748476417 10 Manual.Count131072.C036198.packed 64 cuts36198 = true := by
 decide +kernel
def pointBounds36198 : List (Nat × Nat × Nat) := [(4748574720,107608649804527,107609034550409)]
theorem point_links_checked36198 : (cuts36198.take 1).map (fun c => (4748476417-1+2*2^10*c.k,107608382527793+c.lower,107608767273510+c.upper)) = pointBounds36198 := by
 decide +kernel
def cuts36199 : List PrefixCut := [⟨57,311250518,311250713⟩,
⟨64,349304236,349304454⟩]
theorem checked36199 : checkPrefixCuts (2^48) 4748607489 10 Manual.Count131072.C036199.packed 64 cuts36199 = true := by
 decide +kernel
def pointBounds36199 : List (Nat × Nat × Nat) := [(4748724224,107609046174598,107609430920726)]
theorem point_links_checked36199 : (cuts36199.take 1).map (fun c => (4748607489-1+2*2^10*c.k,107608734924080+c.lower,107609119670013+c.upper)) = pointBounds36199 := by
 decide +kernel
def cuts36200 : List PrefixCut := [⟨64,351665467,351665680⟩]
theorem checked36200 : checkPrefixCuts (2^48) 4748738561 10 Manual.Count131072.C036200.packed 64 cuts36200 = true := by
 decide +kernel
def cuts36201 : List PrefixCut := [⟨2,11143127,11143134⟩,
⟨64,345373021,345373236⟩]
theorem checked36201 : checkPrefixCuts (2^48) 4748869633 10 Manual.Count131072.C036201.packed 64 cuts36201 = true := by
 decide +kernel
def pointBounds36201 : List (Nat × Nat × Nat) := [(4748873728,107609447036910,107609831783281)]
theorem point_links_checked36201 : (cuts36201.take 1).map (fun c => (4748869633-1+2*2^10*c.k,107609435893783+c.lower,107609820640147+c.upper)) = pointBounds36201 := by
 decide +kernel
def cuts36202 : List PrefixCut := [⟨11,60218523,60218558⟩,
⟨64,345126452,345126659⟩]
theorem checked36202 : checkPrefixCuts (2^48) 4749000705 10 Manual.Count131072.C036202.packed 64 cuts36202 = true := by
 decide +kernel
def pointBounds36202 : List (Nat × Nat × Nat) := [(4749023232,107609841485327,107610226231941)]
theorem point_links_checked36202 : (cuts36202.take 1).map (fun c => (4749000705-1+2*2^10*c.k,107609781266804+c.lower,107610166013383+c.upper)) = pointBounds36202 := by
 decide +kernel
def cuts36203 : List PrefixCut := [⟨20,105557103,105557170⟩,
⟨64,343042498,343042711⟩]
theorem checked36203 : checkPrefixCuts (2^48) 4749131777 10 Manual.Count131072.C036203.packed 64 cuts36203 = true := by
 decide +kernel
def pointBounds36203 : List (Nat × Nat × Nat) := [(4749172736,107610231950359,107610616697212)]
theorem point_links_checked36203 : (cuts36203.take 1).map (fun c => (4749131777-1+2*2^10*c.k,107610126393256+c.lower,107610511140042+c.upper)) = pointBounds36203 := by
 decide +kernel
def cuts36204 : List PrefixCut := [⟨29,160968363,160968459⟩,
⟨64,354649258,354649475⟩]
theorem checked36204 : checkPrefixCuts (2^48) 4749262849 10 Manual.Count131072.C036204.packed 64 cuts36204 = true := by
 decide +kernel
def pointBounds36204 : List (Nat × Nat × Nat) := [(4749322240,107610630404117,107611015151212)]
theorem point_links_checked36204 : (cuts36204.take 1).map (fun c => (4749262849-1+2*2^10*c.k,107610469435754+c.lower,107610854182753+c.upper)) = pointBounds36204 := by
 decide +kernel
def cuts36205 : List PrefixCut := [⟨38,206716151,206716286⟩,
⟨64,344445994,344446213⟩]
theorem checked36205 : checkPrefixCuts (2^48) 4749393921 10 Manual.Count131072.C036205.packed 64 cuts36205 = true := by
 decide +kernel
def pointBounds36205 : List (Nat × Nat × Nat) := [(4749471744,107611030801163,107611415548514)]
theorem point_links_checked36205 : (cuts36205.take 1).map (fun c => (4749393921-1+2*2^10*c.k,107610824085012+c.lower,107611208832228+c.upper)) = pointBounds36205 := by
 decide +kernel
def cuts36206 : List PrefixCut := [⟨47,254594690,254594845⟩,
⟨64,349533021,349533235⟩]
theorem checked36206 : checkPrefixCuts (2^48) 4749524993 10 Manual.Count131072.C036206.packed 64 cuts36206 = true := by
 decide +kernel
def pointBounds36206 : List (Nat × Nat × Nat) := [(4749621248,107611423125696,107611807873286)]
theorem point_links_checked36206 : (cuts36206.take 1).map (fun c => (4749524993-1+2*2^10*c.k,107611168531006+c.lower,107611553278441+c.upper)) = pointBounds36206 := by
 decide +kernel
def cuts36207 : List PrefixCut := [⟨56,298203597,298203784⟩,
⟨64,343063893,343064108⟩]
theorem checked36207 : checkPrefixCuts (2^48) 4749656065 10 Manual.Count131072.C036207.packed 64 cuts36207 = true := by
 decide +kernel
def pointBounds36207 : List (Nat × Nat × Nat) := [(4749770752,107611816267624,107612201015460)]
theorem point_links_checked36207 : (cuts36207.take 1).map (fun c => (4749656065-1+2*2^10*c.k,107611518064027+c.lower,107611902811676+c.upper)) = pointBounds36207 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000193
