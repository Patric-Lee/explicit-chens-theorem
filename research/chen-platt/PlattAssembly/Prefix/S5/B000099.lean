import PlattAssemblyKernel
import PlattCertificates.Count131072.C043168
import PlattCertificates.Count131072.C043169
import PlattCertificates.Count131072.C043170
import PlattCertificates.Count131072.C043171
import PlattCertificates.Count131072.C043172
import PlattCertificates.Count131072.C043173
import PlattCertificates.Count131072.C043174
import PlattCertificates.Count131072.C043175
import PlattCertificates.Count131072.C043176
import PlattCertificates.Count131072.C043177
import PlattCertificates.Count131072.C043178
import PlattCertificates.Count131072.C043179
import PlattCertificates.Count131072.C043180
import PlattCertificates.Count131072.C043181
import PlattCertificates.Count131072.C043182
import PlattCertificates.Count131072.C043183
import PlattCertificates.Count131072.C043184
import PlattCertificates.Count131072.C043185
import PlattCertificates.Count131072.C043186
import PlattCertificates.Count131072.C043187
import PlattCertificates.Count131072.C043188
import PlattCertificates.Count131072.C043189
import PlattCertificates.Count131072.C043190
import PlattCertificates.Count131072.C043191
import PlattCertificates.Count131072.C043192
import PlattCertificates.Count131072.C043193
import PlattCertificates.Count131072.C043194
import PlattCertificates.Count131072.C043195
import PlattCertificates.Count131072.C043196
import PlattCertificates.Count131072.C043197
import PlattCertificates.Count131072.C043198
import PlattCertificates.Count131072.C043199
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000099
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43168 : List PrefixCut := [⟨64,289274041,289274212⟩]
theorem checked43168 : checkPrefixCuts (2^48) 5662048257 10 Manual.Count131072.C043168.packed 64 cuts43168 = true := by
 decide +kernel
def cuts43169 : List PrefixCut := [⟨20,90424725,90424775⟩,
⟨64,291852251,291852418⟩]
theorem checked43169 : checkPrefixCuts (2^48) 5662179329 10 Manual.Count131072.C043169.packed 64 cuts43169 = true := by
 decide +kernel
def pointBounds43169 : List (Nat × Nat × Nat) := [(5662220288,109822889627782,109823275695874)]
theorem point_links_checked43169 : (cuts43169.take 1).map (fun c => (5662179329-1+2*2^10*c.k,109822799203057+c.lower,109823185271099+c.upper)) = pointBounds43169 := by
 decide +kernel
def cuts43170 : List PrefixCut := [⟨43,194514713,194514826⟩,
⟨64,289360047,289360218⟩]
theorem checked43170 : checkPrefixCuts (2^48) 5662310401 10 Manual.Count131072.C043170.packed 64 cuts43170 = true := by
 decide +kernel
def pointBounds43170 : List (Nat × Nat × Nat) := [(5662398464,109823285570021,109823671638343)]
theorem point_links_checked43170 : (cuts43170.take 1).map (fun c => (5662310401-1+2*2^10*c.k,109823091055308+c.lower,109823477123517+c.upper)) = pointBounds43170 := by
 decide +kernel
def cuts43171 : List PrefixCut := [⟨64,289651612,289651783⟩]
theorem checked43171 : checkPrefixCuts (2^48) 5662441473 10 Manual.Count131072.C043171.packed 64 cuts43171 = true := by
 decide +kernel
def cuts43172 : List PrefixCut := [⟨2,9245676,9245681⟩,
⟨64,291981153,291981317⟩]
theorem checked43172 : checkPrefixCuts (2^48) 5662572545 10 Manual.Count131072.C043172.packed 64 cuts43172 = true := by
 decide +kernel
def pointBounds43172 : List (Nat × Nat × Nat) := [(5662576640,109823679312643,109824065381199)]
theorem point_links_checked43172 : (cuts43172.take 1).map (fun c => (5662572545-1+2*2^10*c.k,109823670066967+c.lower,109824056135518+c.upper)) = pointBounds43172 := by
 decide +kernel
def cuts43173 : List PrefixCut := [⟨25,114176017,114176082⟩,
⟨64,287997911,287998082⟩]
theorem checked43173 : checkPrefixCuts (2^48) 5662703617 10 Manual.Count131072.C043173.packed 64 cuts43173 = true := by
 decide +kernel
def pointBounds43173 : List (Nat × Nat × Nat) := [(5662754816,109824076224137,109824462292917)]
theorem point_links_checked43173 : (cuts43173.take 1).map (fun c => (5662703617-1+2*2^10*c.k,109823962048120+c.lower,109824348116835+c.upper)) = pointBounds43173 := by
 decide +kernel
def cuts43174 : List PrefixCut := [⟨48,215074493,215074619⟩,
⟨64,288537963,288538130⟩]
theorem checked43174 : checkPrefixCuts (2^48) 5662834689 10 Manual.Count131072.C043174.packed 64 cuts43174 = true := by
 decide +kernel
def pointBounds43174 : List (Nat × Nat × Nat) := [(5662932992,109824465120524,109824851189536)]
theorem point_links_checked43174 : (cuts43174.take 1).map (fun c => (5662834689-1+2*2^10*c.k,109824250046031+c.lower,109824636114917+c.upper)) = pointBounds43174 := by
 decide +kernel
def cuts43175 : List PrefixCut := [⟨64,288382210,288382382⟩]
theorem checked43175 : checkPrefixCuts (2^48) 5662965761 10 Manual.Count131072.C043175.packed 64 cuts43175 = true := by
 decide +kernel
def cuts43176 : List PrefixCut := [⟨7,33152094,33152114⟩,
⟨64,292351757,292351932⟩]
theorem checked43176 : checkPrefixCuts (2^48) 5663096833 10 Manual.Count131072.C043176.packed 64 cuts43176 = true := by
 decide +kernel
def pointBounds43176 : List (Nat × Nat × Nat) := [(5663111168,109824860118298,109825246187543)]
theorem point_links_checked43176 : (cuts43176.take 1).map (fun c => (5663096833-1+2*2^10*c.k,109824826966204+c.lower,109825213035429+c.upper)) = pointBounds43176 := by
 decide +kernel
def cuts43177 : List PrefixCut := [⟨30,135487471,135487545⟩,
⟨64,289064671,289064833⟩]
theorem checked43177 : checkPrefixCuts (2^48) 5663227905 10 Manual.Count131072.C043177.packed 64 cuts43177 = true := by
 decide +kernel
def pointBounds43177 : List (Nat × Nat × Nat) := [(5663289344,109825254805432,109825640874906)]
theorem point_links_checked43177 : (cuts43177.take 1).map (fun c => (5663227905-1+2*2^10*c.k,109825119317961+c.lower,109825505387361+c.upper)) = pointBounds43177 := by
 decide +kernel
def cuts43178 : List PrefixCut := [⟨53,239904655,239904794⟩,
⟨64,289902854,289903023⟩]
theorem checked43178 : checkPrefixCuts (2^48) 5663358977 10 Manual.Count131072.C043178.packed 64 cuts43178 = true := by
 decide +kernel
def pointBounds43178 : List (Nat × Nat × Nat) := [(5663467520,109825648287287,109826034356988)]
theorem point_links_checked43178 : (cuts43178.take 1).map (fun c => (5663358977-1+2*2^10*c.k,109825408382632+c.lower,109825794452194+c.upper)) = pointBounds43178 := by
 decide +kernel
def cuts43179 : List PrefixCut := [⟨64,292480552,292480723⟩]
theorem checked43179 : checkPrefixCuts (2^48) 5663490049 10 Manual.Count131072.C043179.packed 64 cuts43179 = true := by
 decide +kernel
def cuts43180 : List PrefixCut := [⟨12,54171523,54171555⟩,
⟨64,289392473,289392646⟩]
theorem checked43180 : checkPrefixCuts (2^48) 5663621121 10 Manual.Count131072.C043180.packed 64 cuts43180 = true := by
 decide +kernel
def pointBounds43180 : List (Nat × Nat × Nat) := [(5663645696,109826044937561,109826431007495)]
theorem point_links_checked43180 : (cuts43180.take 1).map (fun c => (5663621121-1+2*2^10*c.k,109825990766038+c.lower,109826376835940+c.upper)) = pointBounds43180 := by
 decide +kernel
def cuts43181 : List PrefixCut := [⟨35,160472531,160472621⟩,
⟨64,292317899,292318066⟩]
theorem checked43181 : checkPrefixCuts (2^48) 5663752193 10 Manual.Count131072.C043181.packed 64 cuts43181 = true := by
 decide +kernel
def pointBounds43181 : List (Nat × Nat × Nat) := [(5663823872,109826440631042,109826826701207)]
theorem point_links_checked43181 : (cuts43181.take 1).map (fun c => (5663752193-1+2*2^10*c.k,109826280158511+c.lower,109826666228586+c.upper)) = pointBounds43181 := by
 decide +kernel
def cuts43182 : List PrefixCut := [⟨58,261649055,261649211⟩,
⟨64,287788813,287788983⟩]
theorem checked43182 : checkPrefixCuts (2^48) 5663883265 10 Manual.Count131072.C043182.packed 64 cuts43182 = true := by
 decide +kernel
def pointBounds43182 : List (Nat × Nat × Nat) := [(5664002048,109826834125465,109827220195863)]
theorem point_links_checked43182 : (cuts43182.take 1).map (fun c => (5663883265-1+2*2^10*c.k,109826572476410+c.lower,109826958546652+c.upper)) = pointBounds43182 := by
 decide +kernel
def cuts43183 : List PrefixCut := [⟨64,285993147,285993318⟩]
theorem checked43183 : checkPrefixCuts (2^48) 5664014337 10 Manual.Count131072.C043183.packed 64 cuts43183 = true := by
 decide +kernel
def cuts43184 : List PrefixCut := [⟨17,78118965,78119009⟩,
⟨64,294036892,294037064⟩]
theorem checked43184 : checkPrefixCuts (2^48) 5664145409 10 Manual.Count131072.C043184.packed 64 cuts43184 = true := by
 decide +kernel
def pointBounds43184 : List (Nat × Nat × Nat) := [(5664180224,109827224377335,109827610447962)]
theorem point_links_checked43184 : (cuts43184.take 1).map (fun c => (5664145409-1+2*2^10*c.k,109827146258370+c.lower,109827532328953+c.upper)) = pointBounds43184 := by
 decide +kernel
def cuts43185 : List PrefixCut := [⟨40,184160933,184161044⟩,
⟨64,292638715,292638887⟩]
theorem checked43185 : checkPrefixCuts (2^48) 5664276481 10 Manual.Count131072.C043185.packed 64 cuts43185 = true := by
 decide +kernel
def pointBounds43185 : List (Nat × Nat × Nat) := [(5664358400,109827624456195,109828010527061)]
theorem point_links_checked43185 : (cuts43185.take 1).map (fun c => (5664276481-1+2*2^10*c.k,109827440295262+c.lower,109827826366017+c.upper)) = pointBounds43185 := by
 decide +kernel
def cuts43186 : List PrefixCut := [⟨63,284035360,284035530⟩,
⟨64,288408142,288408315⟩]
theorem checked43186 : checkPrefixCuts (2^48) 5664407553 10 Manual.Count131072.C043186.packed 64 cuts43186 = true := by
 decide +kernel
def pointBounds43186 : List (Nat × Nat × Nat) := [(5664536576,109828016969337,109828403040434)]
theorem point_links_checked43186 : (cuts43186.take 1).map (fun c => (5664407553-1+2*2^10*c.k,109827732933977+c.lower,109828119004904+c.upper)) = pointBounds43186 := by
 decide +kernel
def cuts43187 : List PrefixCut := [⟨64,291333243,291333414⟩]
theorem checked43187 : checkPrefixCuts (2^48) 5664538625 10 Manual.Count131072.C043187.packed 64 cuts43187 = true := by
 decide +kernel
def cuts43188 : List PrefixCut := [⟨22,100024665,100024723⟩,
⟨64,291674284,291674452⟩]
theorem checked43188 : checkPrefixCuts (2^48) 5664669697 10 Manual.Count131072.C043188.packed 64 cuts43188 = true := by
 decide +kernel
def pointBounds43188 : List (Nat × Nat × Nat) := [(5664714752,109828412700027,109828798771356)]
theorem point_links_checked43188 : (cuts43188.take 1).map (fun c => (5664669697-1+2*2^10*c.k,109828312675362+c.lower,109828698746633+c.upper)) = pointBounds43188 := by
 decide +kernel
def cuts43189 : List PrefixCut := [⟨45,204466110,204466231⟩,
⟨64,291071289,291071458⟩]
theorem checked43189 : checkPrefixCuts (2^48) 5664800769 10 Manual.Count131072.C043189.packed 64 cuts43189 = true := by
 decide +kernel
def pointBounds43189 : List (Nat × Nat × Nat) := [(5664892928,109828808815756,109829194887316)]
theorem point_links_checked43189 : (cuts43189.take 1).map (fun c => (5664800769-1+2*2^10*c.k,109828604349646+c.lower,109828990421085+c.upper)) = pointBounds43189 := by
 decide +kernel
def cuts43190 : List PrefixCut := [⟨64,292306692,292306865⟩]
theorem checked43190 : checkPrefixCuts (2^48) 5664931841 10 Manual.Count131072.C043190.packed 64 cuts43190 = true := by
 decide +kernel
def cuts43191 : List PrefixCut := [⟨4,17886984,17886993⟩,
⟨64,289070390,289070554⟩]
theorem checked43191 : checkPrefixCuts (2^48) 5665062913 10 Manual.Count131072.C043191.packed 64 cuts43191 = true := by
 decide +kernel
def pointBounds43191 : List (Nat × Nat × Nat) := [(5665071104,109829205614611,109829591686401)]
theorem point_links_checked43191 : (cuts43191.take 1).map (fun c => (5665062913-1+2*2^10*c.k,109829187727627+c.lower,109829573799408+c.upper)) = pointBounds43191 := by
 decide +kernel
def cuts43192 : List PrefixCut := [⟨27,124211779,124211852⟩,
⟨64,296715106,296715278⟩]
theorem checked43192 : checkPrefixCuts (2^48) 5665193985 10 Manual.Count131072.C043192.packed 64 cuts43192 = true := by
 decide +kernel
def pointBounds43192 : List (Nat × Nat × Nat) := [(5665249280,109829601009796,109829987081814)]
theorem point_links_checked43192 : (cuts43192.take 1).map (fun c => (5665193985-1+2*2^10*c.k,109829476798017+c.lower,109829862869962+c.upper)) = pointBounds43192 := by
 decide +kernel
def cuts43193 : List PrefixCut := [⟨50,225463047,225463174⟩,
⟨64,288212397,288212561⟩]
theorem checked43193 : checkPrefixCuts (2^48) 5665325057 10 Manual.Count131072.C043193.packed 64 cuts43193 = true := by
 decide +kernel
def pointBounds43193 : List (Nat × Nat × Nat) := [(5665427456,109829998976170,109830385048414)]
theorem point_links_checked43193 : (cuts43193.take 1).map (fun c => (5665325057-1+2*2^10*c.k,109829773513123+c.lower,109830159585240+c.upper)) = pointBounds43193 := by
 decide +kernel
def cuts43194 : List PrefixCut := [⟨64,289000642,289000813⟩]
theorem checked43194 : checkPrefixCuts (2^48) 5665456129 10 Manual.Count131072.C043194.packed 64 cuts43194 = true := by
 decide +kernel
def cuts43195 : List PrefixCut := [⟨9,40738768,40738792⟩,
⟨64,285963447,285963617⟩]
theorem checked43195 : checkPrefixCuts (2^48) 5665587201 10 Manual.Count131072.C043195.packed 64 cuts43195 = true := by
 decide +kernel
def pointBounds43195 : List (Nat × Nat × Nat) := [(5665605632,109830391464930,109830777537406)]
theorem point_links_checked43195 : (cuts43195.take 1).map (fun c => (5665587201-1+2*2^10*c.k,109830350726162+c.lower,109830736798614+c.upper)) = pointBounds43195 := by
 decide +kernel
def cuts43196 : List PrefixCut := [⟨32,144817409,144817495⟩,
⟨64,291024167,291024339⟩]
theorem checked43196 : checkPrefixCuts (2^48) 5665718273 10 Manual.Count131072.C043196.packed 64 cuts43196 = true := by
 decide +kernel
def pointBounds43196 : List (Nat × Nat × Nat) := [(5665783808,109830781507018,109831167579726)]
theorem point_links_checked43196 : (cuts43196.take 1).map (fun c => (5665718273-1+2*2^10*c.k,109830636689609+c.lower,109831022762231+c.upper)) = pointBounds43196 := by
 decide +kernel
def cuts43197 : List PrefixCut := [⟨55,249238077,249238228⟩,
⟨64,289079945,289080115⟩]
theorem checked43197 : checkPrefixCuts (2^48) 5665849345 10 Manual.Count131072.C043197.packed 64 cuts43197 = true := by
 decide +kernel
def pointBounds43197 : List (Nat × Nat × Nat) := [(5665961984,109831176951853,109831563024798)]
theorem point_links_checked43197 : (cuts43197.take 1).map (fun c => (5665849345-1+2*2^10*c.k,109830927713776+c.lower,109831313786570+c.upper)) = pointBounds43197 := by
 decide +kernel
def cuts43198 : List PrefixCut := [⟨64,293444903,293445079⟩]
theorem checked43198 : checkPrefixCuts (2^48) 5665980417 10 Manual.Count131072.C043198.packed 64 cuts43198 = true := by
 decide +kernel
def cuts43199 : List PrefixCut := [⟨14,63983693,63983732⟩,
⟨64,289364635,289364799⟩]
theorem checked43199 : checkPrefixCuts (2^48) 5666111489 10 Manual.Count131072.C043199.packed 64 cuts43199 = true := by
 decide +kernel
def pointBounds43199 : List (Nat × Nat × Nat) := [(5666140160,109831574222317,109831960295496)]
theorem point_links_checked43199 : (cuts43199.take 1).map (fun c => (5666111489-1+2*2^10*c.k,109831510238624+c.lower,109831896311764+c.upper)) = pointBounds43199 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000099
