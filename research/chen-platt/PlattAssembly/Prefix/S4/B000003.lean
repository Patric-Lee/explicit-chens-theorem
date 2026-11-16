import PlattAssemblyKernel
import PlattCertificates.Count131072.C030096
import PlattCertificates.Count131072.C030097
import PlattCertificates.Count131072.C030098
import PlattCertificates.Count131072.C030099
import PlattCertificates.Count131072.C030100
import PlattCertificates.Count131072.C030101
import PlattCertificates.Count131072.C030102
import PlattCertificates.Count131072.C030103
import PlattCertificates.Count131072.C030104
import PlattCertificates.Count131072.C030105
import PlattCertificates.Count131072.C030106
import PlattCertificates.Count131072.C030107
import PlattCertificates.Count131072.C030108
import PlattCertificates.Count131072.C030109
import PlattCertificates.Count131072.C030110
import PlattCertificates.Count131072.C030111
import PlattCertificates.Count131072.C030112
import PlattCertificates.Count131072.C030113
import PlattCertificates.Count131072.C030114
import PlattCertificates.Count131072.C030115
import PlattCertificates.Count131072.C030116
import PlattCertificates.Count131072.C030117
import PlattCertificates.Count131072.C030118
import PlattCertificates.Count131072.C030119
import PlattCertificates.Count131072.C030120
import PlattCertificates.Count131072.C030121
import PlattCertificates.Count131072.C030122
import PlattCertificates.Count131072.C030123
import PlattCertificates.Count131072.C030124
import PlattCertificates.Count131072.C030125
import PlattCertificates.Count131072.C030126
import PlattCertificates.Count131072.C030127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30096 : List PrefixCut := [⟨58,192606234,192606344⟩,
⟨128,423344971,423345207⟩]
theorem checked30096 : checkPrefixCuts (2^48) 3948675073 9 Manual.Count131072.C030096.packed 128 cuts30096 = true := by
 decide +kernel
def pointBounds30096 : List (Nat × Nat × Nat) := [(3948734464,105268831781409,105269215125661)]
theorem point_links_checked30096 : (cuts30096.take 1).map (fun c => (3948675073-1+2*2^9*c.k,105268639175175+c.lower,105269022519317+c.upper)) = pointBounds30096 := by
 decide +kernel
def cuts30097 : List PrefixCut := [⟨51,171928667,171928764⟩,
⟨128,425968290,425968534⟩]
theorem checked30097 : checkPrefixCuts (2^48) 3948806145 9 Manual.Count131072.C030097.packed 128 cuts30097 = true := by
 decide +kernel
def pointBounds30097 : List (Nat × Nat × Nat) := [(3948858368,105269234448813,105269617793288)]
theorem point_links_checked30097 : (cuts30097.take 1).map (fun c => (3948806145-1+2*2^9*c.k,105269062520146+c.lower,105269445864524+c.upper)) = pointBounds30097 := by
 decide +kernel
def cuts30098 : List PrefixCut := [⟨44,146191673,146191754⟩,
⟨128,424813718,424813960⟩]
theorem checked30098 : checkPrefixCuts (2^48) 3948937217 9 Manual.Count131072.C030098.packed 128 cuts30098 = true := by
 decide +kernel
def pointBounds30098 : List (Nat × Nat × Nat) := [(3948982272,105269634680109,105270018024812)]
theorem point_links_checked30098 : (cuts30098.take 1).map (fun c => (3948937217-1+2*2^9*c.k,105269488488436+c.lower,105269871833058+c.upper)) = pointBounds30098 := by
 decide +kernel
def cuts30099 : List PrefixCut := [⟨37,120527616,120527685⟩,
⟨128,421378401,421378637⟩]
theorem checked30099 : checkPrefixCuts (2^48) 3949068289 9 Manual.Count131072.C030099.packed 128 cuts30099 = true := by
 decide +kernel
def pointBounds30099 : List (Nat × Nat × Nat) := [(3949106176,105270033829770,105270417174703)]
theorem point_links_checked30099 : (cuts30099.take 1).map (fun c => (3949068289-1+2*2^9*c.k,105269913302154+c.lower,105270296647018+c.upper)) = pointBounds30099 := by
 decide +kernel
def cuts30100 : List PrefixCut := [⟨30,99141629,99141684⟩,
⟨128,424785490,424785721⟩]
theorem checked30100 : checkPrefixCuts (2^48) 3949199361 9 Manual.Count131072.C030100.packed 128 cuts30100 = true := by
 decide +kernel
def pointBounds30100 : List (Nat × Nat × Nat) := [(3949230080,105270433822184,105270817167339)]
theorem point_links_checked30100 : (cuts30100.take 1).map (fun c => (3949199361-1+2*2^9*c.k,105270334680555+c.lower,105270718025655+c.upper)) = pointBounds30100 := by
 decide +kernel
def cuts30101 : List PrefixCut := [⟨23,74050922,74050960⟩,
⟨128,423274706,423274938⟩]
theorem checked30101 : checkPrefixCuts (2^48) 3949330433 9 Manual.Count131072.C030101.packed 128 cuts30101 = true := by
 decide +kernel
def pointBounds30101 : List (Nat × Nat × Nat) := [(3949353984,105270833516967,105271216862336)]
theorem point_links_checked30101 : (cuts30101.take 1).map (fun c => (3949330433-1+2*2^9*c.k,105270759466045+c.lower,105271142811376+c.upper)) = pointBounds30101 := by
 decide +kernel
def cuts30102 : List PrefixCut := [⟨16,51598783,51598813⟩,
⟨128,426325146,426325383⟩]
theorem checked30102 : checkPrefixCuts (2^48) 3949461505 9 Manual.Count131072.C030102.packed 128 cuts30102 = true := by
 decide +kernel
def pointBounds30102 : List (Nat × Nat × Nat) := [(3949477888,105271234339534,105271617685127)]
theorem point_links_checked30102 : (cuts30102.take 1).map (fun c => (3949461505-1+2*2^9*c.k,105271182740751+c.lower,105271566086314+c.upper)) = pointBounds30102 := by
 decide +kernel
def cuts30103 : List PrefixCut := [⟨9,30430898,30430915⟩,
⟨128,427380056,427380296⟩]
theorem checked30103 : checkPrefixCuts (2^48) 3949592577 9 Manual.Count131072.C030103.packed 128 cuts30103 = true := by
 decide +kernel
def pointBounds30103 : List (Nat × Nat × Nat) := [(3949601792,105271639496795,105272022842612)]
theorem point_links_checked30103 : (cuts30103.take 1).map (fun c => (3949592577-1+2*2^9*c.k,105271609065897+c.lower,105271992411697+c.upper)) = pointBounds30103 := by
 decide +kernel
def cuts30104 : List PrefixCut := [⟨2,6413799,6413803⟩,
⟨123,405987113,405987345⟩,
⟨128,422234880,422235122⟩]
theorem checked30104 : checkPrefixCuts (2^48) 3949723649 9 Manual.Count131072.C030104.packed 128 cuts30104 = true := by
 decide +kernel
def pointBounds30104 : List (Nat × Nat × Nat) := [(3949725696,105272042859752,105272426205796),(3949849600,105272442433066,105272825779338)]
theorem point_links_checked30104 : (cuts30104.take 2).map (fun c => (3949723649-1+2*2^9*c.k,105272036445953+c.lower,105272419791993+c.upper)) = pointBounds30104 := by
 decide +kernel
def cuts30105 : List PrefixCut := [⟨116,388158786,388159004⟩,
⟨128,428349332,428349573⟩]
theorem checked30105 : checkPrefixCuts (2^48) 3949854721 9 Manual.Count131072.C030105.packed 128 cuts30105 = true := by
 decide +kernel
def pointBounds30105 : List (Nat × Nat × Nat) := [(3949973504,105272846839619,105273230186119)]
theorem point_links_checked30105 : (cuts30105.take 1).map (fun c => (3949854721-1+2*2^9*c.k,105272458680833+c.lower,105272842027115+c.upper)) = pointBounds30105 := by
 decide +kernel
def cuts30106 : List PrefixCut := [⟨109,359927830,359928035⟩,
⟨128,426054822,426055064⟩]
theorem checked30106 : checkPrefixCuts (2^48) 3949985793 9 Manual.Count131072.C030106.packed 128 cuts30106 = true := by
 decide +kernel
def pointBounds30106 : List (Nat × Nat × Nat) := [(3950097408,105273246957995,105273630304723)]
theorem point_links_checked30106 : (cuts30106.take 1).map (fun c => (3949985793-1+2*2^9*c.k,105272887030165+c.lower,105273270376688+c.upper)) = pointBounds30106 := by
 decide +kernel
def cuts30107 : List PrefixCut := [⟨102,333266215,333266404⟩,
⟨128,419627559,419627795⟩]
theorem checked30107 : checkPrefixCuts (2^48) 3950116865 9 Manual.Count131072.C030107.packed 128 cuts30107 = true := by
 decide +kernel
def pointBounds30107 : List (Nat × Nat × Nat) := [(3950221312,105273646351202,105274029698156)]
theorem point_links_checked30107 : (cuts30107.take 1).map (fun c => (3950116865-1+2*2^9*c.k,105273313084987+c.lower,105273696431752+c.upper)) = pointBounds30107 := by
 decide +kernel
def cuts30108 : List PrefixCut := [⟨95,311594237,311594410⟩,
⟨128,417333591,417333823⟩]
theorem checked30108 : checkPrefixCuts (2^48) 3950247937 9 Manual.Count131072.C030108.packed 128 cuts30108 = true := by
 decide +kernel
def pointBounds30108 : List (Nat × Nat × Nat) := [(3950345216,105274044306783,105274427653957)]
theorem point_links_checked30108 : (cuts30108.take 1).map (fun c => (3950247937-1+2*2^9*c.k,105273732712546+c.lower,105274116059547+c.upper)) = pointBounds30108 := by
 decide +kernel
def cuts30109 : List PrefixCut := [⟨88,296051334,296051499⟩,
⟨128,429147527,429147770⟩]
theorem checked30109 : checkPrefixCuts (2^48) 3950379009 9 Manual.Count131072.C030109.packed 128 cuts30109 = true := by
 decide +kernel
def pointBounds30109 : List (Nat × Nat × Nat) := [(3950469120,105274446097471,105274829444869)]
theorem point_links_checked30109 : (cuts30109.take 1).map (fun c => (3950379009-1+2*2^9*c.k,105274150046137+c.lower,105274533393370+c.upper)) = pointBounds30109 := by
 decide +kernel
def cuts30110 : List PrefixCut := [⟨81,265760683,265760828⟩,
⟨128,424003226,424003462⟩]
theorem checked30110 : checkPrefixCuts (2^48) 3950510081 9 Manual.Count131072.C030110.packed 128 cuts30110 = true := by
 decide +kernel
def pointBounds30110 : List (Nat × Nat × Nat) := [(3950593024,105274844954347,105275228301968)]
theorem point_links_checked30110 : (cuts30110.take 1).map (fun c => (3950510081-1+2*2^9*c.k,105274579193664+c.lower,105274962541140+c.upper)) = pointBounds30110 := by
 decide +kernel
def cuts30111 : List PrefixCut := [⟨74,239675636,239675771⟩,
⟨128,417790748,417790986⟩]
theorem checked30111 : checkPrefixCuts (2^48) 3950641153 9 Manual.Count131072.C030111.packed 128 cuts30111 = true := by
 decide +kernel
def pointBounds30111 : List (Nat × Nat × Nat) := [(3950716928,105275242872526,105275626220373)]
theorem point_links_checked30111 : (cuts30111.take 1).map (fun c => (3950641153-1+2*2^9*c.k,105275003196890+c.lower,105275386544602+c.upper)) = pointBounds30111 := by
 decide +kernel
def cuts30112 : List PrefixCut := [⟨67,220360545,220360668⟩,
⟨128,425471279,425471512⟩]
theorem checked30112 : checkPrefixCuts (2^48) 3950772225 9 Manual.Count131072.C030112.packed 128 cuts30112 = true := by
 decide +kernel
def pointBounds30112 : List (Nat × Nat × Nat) := [(3950840832,105275641348183,105276024696256)]
theorem point_links_checked30112 : (cuts30112.take 1).map (fun c => (3950772225-1+2*2^9*c.k,105275420987638+c.lower,105275804335588+c.upper)) = pointBounds30112 := by
 decide +kernel
def cuts30113 : List PrefixCut := [⟨60,198980644,198980750⟩,
⟨128,427879400,427879633⟩]
theorem checked30113 : checkPrefixCuts (2^48) 3950903297 9 Manual.Count131072.C030113.packed 128 cuts30113 = true := by
 decide +kernel
def pointBounds30113 : List (Nat × Nat × Nat) := [(3950964736,105276045439561,105276428787850)]
theorem point_links_checked30113 : (cuts30113.take 1).map (fun c => (3950903297-1+2*2^9*c.k,105275846458917+c.lower,105276229807100+c.upper)) = pointBounds30113 := by
 decide +kernel
def cuts30114 : List PrefixCut := [⟨53,172259120,172259213⟩,
⟨128,418746544,418746772⟩]
theorem checked30114 : checkPrefixCuts (2^48) 3951034369 9 Manual.Count131072.C030114.packed 128 cuts30114 = true := by
 decide +kernel
def pointBounds30114 : List (Nat × Nat × Nat) := [(3951088640,105276446597437,105276829945946)]
theorem point_links_checked30114 : (cuts30114.take 1).map (fun c => (3951034369-1+2*2^9*c.k,105276274338317+c.lower,105276657686733+c.upper)) = pointBounds30114 := by
 decide +kernel
def cuts30115 : List PrefixCut := [⟨46,153517937,153518023⟩,
⟨128,421867105,421867344⟩]
theorem checked30115 : checkPrefixCuts (2^48) 3951165441 9 Manual.Count131072.C030115.packed 128 cuts30115 = true := by
 decide +kernel
def pointBounds30115 : List (Nat × Nat × Nat) := [(3951212544,105276846602798,105277229951528)]
theorem point_links_checked30115 : (cuts30115.take 1).map (fun c => (3951165441-1+2*2^9*c.k,105276693084861+c.lower,105277076433505+c.upper)) = pointBounds30115 := by
 decide +kernel
def cuts30116 : List PrefixCut := [⟨39,128010601,128010673⟩,
⟨128,414658395,414658631⟩]
theorem checked30116 : checkPrefixCuts (2^48) 3951296513 9 Manual.Count131072.C030116.packed 128 cuts30116 = true := by
 decide +kernel
def pointBounds30116 : List (Nat × Nat × Nat) := [(3951336448,105277242962567,105277626311522)]
theorem point_links_checked30116 : (cuts30116.take 1).map (fun c => (3951296513-1+2*2^9*c.k,105277114951966+c.lower,105277498300849+c.upper)) = pointBounds30116 := by
 decide +kernel
def cuts30117 : List PrefixCut := [⟨32,105781644,105781703⟩,
⟨128,421839122,421839362⟩]
theorem checked30117 : checkPrefixCuts (2^48) 3951427585 9 Manual.Count131072.C030117.packed 128 cuts30117 = true := by
 decide +kernel
def pointBounds30117 : List (Nat × Nat × Nat) := [(3951460352,105277635392005,105278018741183)]
theorem point_links_checked30117 : (cuts30117.take 1).map (fun c => (3951427585-1+2*2^9*c.k,105277529610361+c.lower,105277912959480+c.upper)) = pointBounds30117 := by
 decide +kernel
def cuts30118 : List PrefixCut := [⟨25,80704869,80704915⟩,
⟨128,421825042,421825278⟩]
theorem checked30118 : checkPrefixCuts (2^48) 3951558657 9 Manual.Count131072.C030118.packed 128 cuts30118 = true := by
 decide +kernel
def pointBounds30118 : List (Nat × Nat × Nat) := [(3951584256,105278032154352,105278415503757)]
theorem point_links_checked30118 : (cuts30118.take 1).map (fun c => (3951558657-1+2*2^9*c.k,105277951449483+c.lower,105278334798842+c.upper)) = pointBounds30118 := by
 decide +kernel
def cuts30119 : List PrefixCut := [⟨18,59618534,59618566⟩,
⟨128,422879597,422879831⟩]
theorem checked30119 : checkPrefixCuts (2^48) 3951689729 9 Manual.Count131072.C030119.packed 128 cuts30119 = true := by
 decide +kernel
def pointBounds30119 : List (Nat × Nat × Nat) := [(3951708160,105278432893059,105278816242686)]
theorem point_links_checked30119 : (cuts30119.take 1).map (fun c => (3951689729-1+2*2^9*c.k,105278373274525+c.lower,105278756624120+c.upper)) = pointBounds30119 := by
 decide +kernel
def cuts30120 : List PrefixCut := [⟨11,34901003,34901021⟩,
⟨128,421939560,421939800⟩]
theorem checked30120 : checkPrefixCuts (2^48) 3951820801 9 Manual.Count131072.C030120.packed 128 cuts30120 = true := by
 decide +kernel
def pointBounds30120 : List (Nat × Nat × Nat) := [(3951832064,105278831055125,105279214404972)]
theorem point_links_checked30120 : (cuts30120.take 1).map (fun c => (3951820801-1+2*2^9*c.k,105278796154122+c.lower,105279179503951+c.upper)) = pointBounds30120 := by
 decide +kernel
def cuts30121 : List PrefixCut := [⟨4,13105259,13105266⟩,
⟨125,410814960,410815198⟩,
⟨128,421711917,421712161⟩]
theorem checked30121 : checkPrefixCuts (2^48) 3951951873 9 Manual.Count131072.C030121.packed 128 cuts30121 = true := by
 decide +kernel
def pointBounds30121 : List (Nat × Nat × Nat) := [(3951955968,105279231198941,105279614549017),(3952079872,105279628908642,105280012258949)]
theorem point_links_checked30121 : (cuts30121.take 2).map (fun c => (3951951873-1+2*2^9*c.k,105279218093682+c.lower,105279601443751+c.upper)) = pointBounds30121 := by
 decide +kernel
def cuts30122 : List PrefixCut := [⟨118,395346812,395347038⟩,
⟨128,428107847,428108089⟩]
theorem checked30122 : checkPrefixCuts (2^48) 3952082945 9 Manual.Count131072.C030122.packed 128 cuts30122 = true := by
 decide +kernel
def pointBounds30122 : List (Nat × Nat × Nat) := [(3952203776,105280035152411,105280418502950)]
theorem point_links_checked30122 : (cuts30122.take 1).map (fun c => (3952082945-1+2*2^9*c.k,105279639805599+c.lower,105280023155912+c.upper)) = pointBounds30122 := by
 decide +kernel
def cuts30123 : List PrefixCut := [⟨111,363713042,363713244⟩,
⟨128,420259612,420259849⟩]
theorem checked30123 : checkPrefixCuts (2^48) 3952214017 9 Manual.Count131072.C030123.packed 128 cuts30123 = true := by
 decide +kernel
def pointBounds30123 : List (Nat × Nat × Nat) := [(3952327680,105280431626488,105280814977245)]
theorem point_links_checked30123 : (cuts30123.take 1).map (fun c => (3952214017-1+2*2^9*c.k,105280067913446+c.lower,105280451264001+c.upper)) = pointBounds30123 := by
 decide +kernel
def cuts30124 : List PrefixCut := [⟨104,347606412,347606606⟩,
⟨128,426441478,426441716⟩]
theorem checked30124 : checkPrefixCuts (2^48) 3952345089 9 Manual.Count131072.C030124.packed 128 cuts30124 = true := by
 decide +kernel
def pointBounds30124 : List (Nat × Nat × Nat) := [(3952451584,105280835779470,105281219130456)]
theorem point_links_checked30124 : (cuts30124.take 1).map (fun c => (3952345089-1+2*2^9*c.k,105280488173058+c.lower,105280871523850+c.upper)) = pointBounds30124 := by
 decide +kernel
def cuts30125 : List PrefixCut := [⟨97,320747523,320747707⟩,
⟨128,424504499,424504740⟩]
theorem checked30125 : checkPrefixCuts (2^48) 3952476161 9 Manual.Count131072.C030125.packed 128 cuts30125 = true := by
 decide +kernel
def pointBounds30125 : List (Nat × Nat × Nat) := [(3952575488,105281235362059,105281618713273)]
theorem point_links_checked30125 : (cuts30125.take 1).map (fun c => (3952476161-1+2*2^9*c.k,105280914614536+c.lower,105281297965566+c.upper)) = pointBounds30125 := by
 decide +kernel
def cuts30126 : List PrefixCut := [⟨90,298163128,298163288⟩,
⟨128,420787526,420787755⟩]
theorem checked30126 : checkPrefixCuts (2^48) 3952607233 9 Manual.Count131072.C030126.packed 128 cuts30126 = true := by
 decide +kernel
def pointBounds30126 : List (Nat × Nat × Nat) := [(3952699392,105281637282163,105282020633594)]
theorem point_links_checked30126 : (cuts30126.take 1).map (fun c => (3952607233-1+2*2^9*c.k,105281339119035+c.lower,105281722470306+c.upper)) = pointBounds30126 := by
 decide +kernel
def cuts30127 : List PrefixCut := [⟨83,274440790,274440939⟩,
⟨128,424903630,424903866⟩]
theorem checked30127 : checkPrefixCuts (2^48) 3952738305 9 Manual.Count131072.C030127.packed 128 cuts30127 = true := by
 decide +kernel
def pointBounds30127 : List (Nat × Nat × Nat) := [(3952823296,105282034347351,105282417699000)]
theorem point_links_checked30127 : (cuts30127.take 1).map (fun c => (3952738305-1+2*2^9*c.k,105281759906561+c.lower,105282143258061+c.upper)) = pointBounds30127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000003
