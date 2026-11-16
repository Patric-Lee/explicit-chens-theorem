import PlattAssemblyKernel
import PlattCertificates.Count131072.C039120
import PlattCertificates.Count131072.C039121
import PlattCertificates.Count131072.C039122
import PlattCertificates.Count131072.C039123
import PlattCertificates.Count131072.C039124
import PlattCertificates.Count131072.C039125
import PlattCertificates.Count131072.C039126
import PlattCertificates.Count131072.C039127
import PlattCertificates.Count131072.C039128
import PlattCertificates.Count131072.C039129
import PlattCertificates.Count131072.C039130
import PlattCertificates.Count131072.C039131
import PlattCertificates.Count131072.C039132
import PlattCertificates.Count131072.C039133
import PlattCertificates.Count131072.C039134
import PlattCertificates.Count131072.C039135
import PlattCertificates.Count131072.C039136
import PlattCertificates.Count131072.C039137
import PlattCertificates.Count131072.C039138
import PlattCertificates.Count131072.C039139
import PlattCertificates.Count131072.C039140
import PlattCertificates.Count131072.C039141
import PlattCertificates.Count131072.C039142
import PlattCertificates.Count131072.C039143
import PlattCertificates.Count131072.C039144
import PlattCertificates.Count131072.C039145
import PlattCertificates.Count131072.C039146
import PlattCertificates.Count131072.C039147
import PlattCertificates.Count131072.C039148
import PlattCertificates.Count131072.C039149
import PlattCertificates.Count131072.C039150
import PlattCertificates.Count131072.C039151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000285
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39120 : List PrefixCut := [⟨48,243269387,243269532⟩,
⟨64,323846201,323846395⟩]
theorem checked39120 : checkPrefixCuts (2^48) 5131468801 10 Manual.Count131072.C039120.packed 64 cuts39120 = true := by
 decide +kernel
def pointBounds39120 : List (Nat × Nat × Nat) := [(5131567104,108586768868787,108587154207894)]
theorem point_links_checked39120 : (cuts39120.take 1).map (fun c => (5131468801-1+2*2^10*c.k,108586525599400+c.lower,108586910938362+c.upper)) = pointBounds39120 := by
 decide +kernel
def cuts39121 : List PrefixCut := [⟨63,320985772,320985966⟩,
⟨64,325593164,325593361⟩]
theorem checked39121 : checkPrefixCuts (2^48) 5131599873 10 Manual.Count131072.C039121.packed 64 cuts39121 = true := by
 decide +kernel
def pointBounds39121 : List (Nat × Nat × Nat) := [(5131728896,108587170431373,108587555770723)]
theorem point_links_checked39121 : (cuts39121.take 1).map (fun c => (5131599873-1+2*2^10*c.k,108586849445601+c.lower,108587234784757+c.upper)) = pointBounds39121 := by
 decide +kernel
def cuts39122 : List PrefixCut := [⟨64,314998887,314999079⟩]
theorem checked39122 : checkPrefixCuts (2^48) 5131730945 10 Manual.Count131072.C039122.packed 64 cuts39122 = true := by
 decide +kernel
def cuts39123 : List PrefixCut := [⟨14,70589815,70589857⟩,
⟨64,321956565,321956757⟩]
theorem checked39123 : checkPrefixCuts (2^48) 5131862017 10 Manual.Count131072.C039123.packed 64 cuts39123 = true := by
 decide +kernel
def pointBounds39123 : List (Nat × Nat × Nat) := [(5131890688,108587560627467,108587945967054)]
theorem point_links_checked39123 : (cuts39123.take 1).map (fun c => (5131862017-1+2*2^10*c.k,108587490037652+c.lower,108587875377197+c.upper)) = pointBounds39123 := by
 decide +kernel
def cuts39124 : List PrefixCut := [⟨29,146056961,146057047⟩,
⟨64,321399870,321400061⟩]
theorem checked39124 : checkPrefixCuts (2^48) 5131993089 10 Manual.Count131072.C039124.packed 64 cuts39124 = true := by
 decide +kernel
def pointBounds39124 : List (Nat × Nat × Nat) := [(5132052480,108587958051178,108588343391001)]
theorem point_links_checked39124 : (cuts39124.take 1).map (fun c => (5131993089-1+2*2^10*c.k,108587811994217+c.lower,108588197333954+c.upper)) = pointBounds39124 := by
 decide +kernel
def cuts39125 : List PrefixCut := [⟨44,221245565,221245699⟩,
⟨64,322104614,322104808⟩]
theorem checked39125 : checkPrefixCuts (2^48) 5132124161 10 Manual.Count131072.C039125.packed 64 cuts39125 = true := by
 decide +kernel
def pointBounds39125 : List (Nat × Nat × Nat) := [(5132214272,108588354639652,108588739979714)]
theorem point_links_checked39125 : (cuts39125.take 1).map (fun c => (5132124161-1+2*2^10*c.k,108588133394087+c.lower,108588518734015+c.upper)) = pointBounds39125 := by
 decide +kernel
def cuts39126 : List PrefixCut := [⟨59,293139284,293139462⟩,
⟨64,316447534,316447727⟩]
theorem checked39126 : checkPrefixCuts (2^48) 5132255233 10 Manual.Count131072.C039126.packed 64 cuts39126 = true := by
 decide +kernel
def pointBounds39126 : List (Nat × Nat × Nat) := [(5132376064,108588748637985,108589133978285)]
theorem point_links_checked39126 : (cuts39126.take 1).map (fun c => (5132255233-1+2*2^10*c.k,108588455498701+c.lower,108588840838823+c.upper)) = pointBounds39126 := by
 decide +kernel
def cuts39127 : List PrefixCut := [⟨64,316878181,316878368⟩]
theorem checked39127 : checkPrefixCuts (2^48) 5132386305 10 Manual.Count131072.C039127.packed 64 cuts39127 = true := by
 decide +kernel
def cuts39128 : List PrefixCut := [⟨10,50125021,50125052⟩,
⟨64,324492968,324493161⟩]
theorem checked39128 : checkPrefixCuts (2^48) 5132517377 10 Manual.Count131072.C039128.packed 64 cuts39128 = true := by
 decide +kernel
def pointBounds39128 : List (Nat × Nat × Nat) := [(5132537856,108589138949437,108589524289970)]
theorem point_links_checked39128 : (cuts39128.take 1).map (fun c => (5132517377-1+2*2^10*c.k,108589088824416+c.lower,108589474164918+c.upper)) = pointBounds39128 := by
 decide +kernel
def cuts39129 : List PrefixCut := [⟨25,124212181,124212256⟩,
⟨64,320097497,320097689⟩]
theorem checked39129 : checkPrefixCuts (2^48) 5132648449 10 Manual.Count131072.C039129.packed 64 cuts39129 = true := by
 decide +kernel
def pointBounds39129 : List (Nat × Nat × Nat) := [(5132699648,108589537529565,108589922870335)]
theorem point_links_checked39129 : (cuts39129.take 1).map (fun c => (5132648449-1+2*2^10*c.k,108589413317384+c.lower,108589798658079+c.upper)) = pointBounds39129 := by
 decide +kernel
def cuts39130 : List PrefixCut := [⟨40,203504743,203504863⟩,
⟨64,323269950,323270140⟩]
theorem checked39130 : checkPrefixCuts (2^48) 5132779521 10 Manual.Count131072.C039130.packed 64 cuts39130 = true := by
 decide +kernel
def pointBounds39130 : List (Nat × Nat × Nat) := [(5132861440,108589936919624,108590322260631)]
theorem point_links_checked39130 : (cuts39130.take 1).map (fun c => (5132779521-1+2*2^10*c.k,108589733414881+c.lower,108590118755768+c.upper)) = pointBounds39130 := by
 decide +kernel
def cuts39131 : List PrefixCut := [⟨55,274457602,274457764⟩,
⟨64,317778030,317778219⟩]
theorem checked39131 : checkPrefixCuts (2^48) 5132910593 10 Manual.Count131072.C039131.packed 64 cuts39131 = true := by
 decide +kernel
def pointBounds39131 : List (Nat × Nat × Nat) := [(5133023232,108590331142433,108590716483672)]
theorem point_links_checked39131 : (cuts39131.take 1).map (fun c => (5132910593-1+2*2^10*c.k,108590056684831+c.lower,108590442025908+c.upper)) = pointBounds39131 := by
 decide +kernel
def cuts39132 : List PrefixCut := [⟨64,319524588,319524777⟩]
theorem checked39132 : checkPrefixCuts (2^48) 5133041665 10 Manual.Count131072.C039132.packed 64 cuts39132 = true := by
 decide +kernel
def cuts39133 : List PrefixCut := [⟨6,31200784,31200803⟩,
⟨64,322093644,322093839⟩]
theorem checked39133 : checkPrefixCuts (2^48) 5133172737 10 Manual.Count131072.C039133.packed 64 cuts39133 = true := by
 decide +kernel
def pointBounds39133 : List (Nat × Nat × Nat) := [(5133185024,108590725188233,108591110529707)]
theorem point_links_checked39133 : (cuts39133.take 1).map (fun c => (5133172737-1+2*2^10*c.k,108590693987449+c.lower,108591079328904+c.upper)) = pointBounds39133 := by
 decide +kernel
def cuts39134 : List PrefixCut := [⟨21,102976108,102976170⟩,
⟨64,321098422,321098617⟩]
theorem checked39134 : checkPrefixCuts (2^48) 5133303809 10 Manual.Count131072.C039134.packed 64 cuts39134 = true := by
 decide +kernel
def pointBounds39134 : List (Nat × Nat × Nat) := [(5133346816,108591119057201,108591504398913)]
theorem point_links_checked39134 : (cuts39134.take 1).map (fun c => (5133303809-1+2*2^10*c.k,108591016081093+c.lower,108591401422743+c.upper)) = pointBounds39134 := by
 decide +kernel
def cuts39135 : List PrefixCut := [⟨36,182972034,182972142⟩,
⟨64,324380129,324380322⟩]
theorem checked39135 : checkPrefixCuts (2^48) 5133434881 10 Manual.Count131072.C039135.packed 64 cuts39135 = true := by
 decide +kernel
def pointBounds39135 : List (Nat × Nat × Nat) := [(5133508608,108591520151549,108591905493502)]
theorem point_links_checked39135 : (cuts39135.take 1).map (fun c => (5133434881-1+2*2^10*c.k,108591337179515+c.lower,108591722521360+c.upper)) = pointBounds39135 := by
 decide +kernel
def cuts39136 : List PrefixCut := [⟨51,254245444,254245599⟩,
⟨64,320095108,320095304⟩]
theorem checked39136 : checkPrefixCuts (2^48) 5133565953 10 Manual.Count131072.C039136.packed 64 cuts39136 = true := by
 decide +kernel
def pointBounds39136 : List (Nat × Nat × Nat) := [(5133670400,108591915805088,108592301147281)]
theorem point_links_checked39136 : (cuts39136.take 1).map (fun c => (5133565953-1+2*2^10*c.k,108591661559644+c.lower,108592046901682+c.upper)) = pointBounds39136 := by
 decide +kernel
def cuts39137 : List PrefixCut := [⟨64,318058302,318058488⟩]
theorem checked39137 : checkPrefixCuts (2^48) 5133697025 10 Manual.Count131072.C039137.packed 64 cuts39137 = true := by
 decide +kernel
def cuts39138 : List PrefixCut := [⟨2,9978599,9978604⟩,
⟨64,319366019,319366206⟩]
theorem checked39138 : checkPrefixCuts (2^48) 5133828097 10 Manual.Count131072.C039138.packed 64 cuts39138 = true := by
 decide +kernel
def pointBounds39138 : List (Nat × Nat × Nat) := [(5133832192,108592309691653,108592695034078)]
theorem point_links_checked39138 : (cuts39138.take 1).map (fun c => (5133828097-1+2*2^10*c.k,108592299713054+c.lower,108592685055474+c.upper)) = pointBounds39138 := by
 decide +kernel
def cuts39139 : List PrefixCut := [⟨17,85418751,85418801⟩,
⟨64,320289906,320290100⟩]
theorem checked39139 : checkPrefixCuts (2^48) 5133959169 10 Manual.Count131072.C039139.packed 64 cuts39139 = true := by
 decide +kernel
def pointBounds39139 : List (Nat × Nat × Nat) := [(5133993984,108592704497824,108593089840481)]
theorem point_links_checked39139 : (cuts39139.take 1).map (fun c => (5133959169-1+2*2^10*c.k,108592619079073+c.lower,108593004421680+c.upper)) = pointBounds39139 := by
 decide +kernel
def cuts39140 : List PrefixCut := [⟨32,160799777,160799873⟩,
⟨64,319733507,319733698⟩]
theorem checked39140 : checkPrefixCuts (2^48) 5134090241 10 Manual.Count131072.C039140.packed 64 cuts39140 = true := by
 decide +kernel
def pointBounds39140 : List (Nat × Nat × Nat) := [(5134155776,108593100168756,108593485511653)]
theorem point_links_checked39140 : (cuts39140.take 1).map (fun c => (5134090241-1+2*2^10*c.k,108592939368979+c.lower,108593324711780+c.upper)) = pointBounds39140 := by
 decide +kernel
def cuts39141 : List PrefixCut := [⟨47,236998850,236998990⟩,
⟨64,324933459,324933649⟩]
theorem checked39141 : checkPrefixCuts (2^48) 5134221313 10 Manual.Count131072.C039141.packed 64 cuts39141 = true := by
 decide +kernel
def pointBounds39141 : List (Nat × Nat × Nat) := [(5134317568,108593496101336,108593881444468)]
theorem point_links_checked39141 : (cuts39141.take 1).map (fun c => (5134221313-1+2*2^10*c.k,108593259102486+c.lower,108593644445478+c.upper)) = pointBounds39141 := by
 decide +kernel
def cuts39142 : List PrefixCut := [⟨62,315057493,315057678⟩,
⟨64,325199288,325199479⟩]
theorem checked39142 : checkPrefixCuts (2^48) 5134352385 10 Manual.Count131072.C039142.packed 64 cuts39142 = true := by
 decide +kernel
def pointBounds39142 : List (Nat × Nat × Nat) := [(5134479360,108593899093438,108594284436805)]
theorem point_links_checked39142 : (cuts39142.take 1).map (fun c => (5134352385-1+2*2^10*c.k,108593584035945+c.lower,108593969379127+c.upper)) = pointBounds39142 := by
 decide +kernel
def cuts39143 : List PrefixCut := [⟨64,319544519,319544710⟩]
theorem checked39143 : checkPrefixCuts (2^48) 5134483457 10 Manual.Count131072.C039143.packed 64 cuts39143 = true := by
 decide +kernel
def cuts39144 : List PrefixCut := [⟨13,64083349,64083388⟩,
⟨64,321126099,321126293⟩]
theorem checked39144 : checkPrefixCuts (2^48) 5134614529 10 Manual.Count131072.C039144.packed 64 cuts39144 = true := by
 decide +kernel
def pointBounds39144 : List (Nat × Nat × Nat) := [(5134641152,108594292863101,108594678206704)]
theorem point_links_checked39144 : (cuts39144.take 1).map (fun c => (5134614529-1+2*2^10*c.k,108594228779752+c.lower,108594614123316+c.upper)) = pointBounds39144 := by
 decide +kernel
def cuts39145 : List PrefixCut := [⟨28,138797613,138797695⟩,
⟨64,321885310,321885502⟩]
theorem checked39145 : checkPrefixCuts (2^48) 5134745601 10 Manual.Count131072.C039145.packed 64 cuts39145 = true := by
 decide +kernel
def pointBounds39145 : List (Nat × Nat × Nat) := [(5134802944,108594688703464,108595074047304)]
theorem point_links_checked39145 : (cuts39145.take 1).map (fun c => (5134745601-1+2*2^10*c.k,108594549905851+c.lower,108594935249609+c.upper)) = pointBounds39145 := by
 decide +kernel
def cuts39146 : List PrefixCut := [⟨43,212192053,212192179⟩,
⟨64,318533390,318533580⟩]
theorem checked39146 : checkPrefixCuts (2^48) 5134876673 10 Manual.Count131072.C039146.packed 64 cuts39146 = true := by
 decide +kernel
def pointBounds39146 : List (Nat × Nat × Nat) := [(5134964736,108595083983214,108595469327290)]
theorem point_links_checked39146 : (cuts39146.take 1).map (fun c => (5134876673-1+2*2^10*c.k,108594871791161+c.lower,108595257135111+c.upper)) = pointBounds39146 := by
 decide +kernel
def cuts39147 : List PrefixCut := [⟨58,291831116,291831282⟩,
⟨64,322033386,322033571⟩]
theorem checked39147 : checkPrefixCuts (2^48) 5135007745 10 Manual.Count131072.C039147.packed 64 cuts39147 = true := by
 decide +kernel
def pointBounds39147 : List (Nat × Nat × Nat) := [(5135126528,108595482155667,108595867499973)]
theorem point_links_checked39147 : (cuts39147.take 1).map (fun c => (5135007745-1+2*2^10*c.k,108595190324551+c.lower,108595575668691+c.upper)) = pointBounds39147 := by
 decide +kernel
def cuts39148 : List PrefixCut := [⟨64,320435588,320435781⟩]
theorem checked39148 : checkPrefixCuts (2^48) 5135138817 10 Manual.Count131072.C039148.packed 64 cuts39148 = true := by
 decide +kernel
def cuts39149 : List PrefixCut := [⟨9,45548771,45548798⟩,
⟨64,319934116,319934307⟩]
theorem checked39149 : checkPrefixCuts (2^48) 5135269889 10 Manual.Count131072.C039149.packed 64 cuts39149 = true := by
 decide +kernel
def pointBounds39149 : List (Nat × Nat × Nat) := [(5135288320,108595878342296,108596263686841)]
theorem point_links_checked39149 : (cuts39149.take 1).map (fun c => (5135269889-1+2*2^10*c.k,108595832793525+c.lower,108596218138043+c.upper)) = pointBounds39149 := by
 decide +kernel
def cuts39150 : List PrefixCut := [⟨24,120692576,120692650⟩,
⟨64,320200009,320200204⟩]
theorem checked39150 : checkPrefixCuts (2^48) 5135400961 10 Manual.Count131072.C039150.packed 64 cuts39150 = true := by
 decide +kernel
def pointBounds39150 : List (Nat × Nat × Nat) := [(5135450112,108596273420217,108596658765000)]
theorem point_links_checked39150 : (cuts39150.take 1).map (fun c => (5135400961-1+2*2^10*c.k,108596152727641+c.lower,108596538072350+c.upper)) = pointBounds39150 := by
 decide +kernel
def cuts39151 : List PrefixCut := [⟨39,198243684,198243803⟩,
⟨64,322000535,322000728⟩]
theorem checked39151 : checkPrefixCuts (2^48) 5135532033 10 Manual.Count131072.C039151.packed 64 cuts39151 = true := by
 decide +kernel
def pointBounds39151 : List (Nat × Nat × Nat) := [(5135611904,108596671171334,108597056516357)]
theorem point_links_checked39151 : (cuts39151.take 1).map (fun c => (5135532033-1+2*2^10*c.k,108596472927650+c.lower,108596858272554+c.upper)) = pointBounds39151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000285
