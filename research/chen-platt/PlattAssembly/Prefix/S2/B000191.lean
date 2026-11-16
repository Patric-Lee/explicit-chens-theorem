import PlattAssemblyKernel
import PlattCertificates.Count131072.C016112
import PlattCertificates.Count131072.C016113
import PlattCertificates.Count131072.C016114
import PlattCertificates.Count131072.C016115
import PlattCertificates.Count131072.C016116
import PlattCertificates.Count131072.C016117
import PlattCertificates.Count131072.C016118
import PlattCertificates.Count131072.C016119
import PlattCertificates.Count131072.C016120
import PlattCertificates.Count131072.C016121
import PlattCertificates.Count131072.C016122
import PlattCertificates.Count131072.C016123
import PlattCertificates.Count131072.C016124
import PlattCertificates.Count131072.C016125
import PlattCertificates.Count131072.C016126
import PlattCertificates.Count131072.C016127
import PlattCertificates.Count131072.C016128
import PlattCertificates.Count131072.C016129
import PlattCertificates.Count131072.C016130
import PlattCertificates.Count131072.C016131
import PlattCertificates.Count131072.C016132
import PlattCertificates.Count131072.C016133
import PlattCertificates.Count131072.C016134
import PlattCertificates.Count131072.C016135
import PlattCertificates.Count131072.C016136
import PlattCertificates.Count131072.C016137
import PlattCertificates.Count131072.C016138
import PlattCertificates.Count131072.C016139
import PlattCertificates.Count131072.C016140
import PlattCertificates.Count131072.C016141
import PlattCertificates.Count131072.C016142
import PlattCertificates.Count131072.C016143
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000191
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16112 : List PrefixCut := [⟨62,389393375,389393626⟩,
⟨127,801523120,801523642⟩,
⟨128,807509415,807509941⟩]
theorem checked16112 : checkPrefixCuts (2^48) 2115764225 9 Manual.Count131072.C016112.packed 128 cuts16112 = true := by
 decide +kernel
def pointBounds16112 : List (Nat × Nat × Nat) := [(2115827712,97206488218472,97206866865350),(2115894272,97206900348217,97207278995366)]
theorem point_links_checked16112 : (cuts16112.take 2).map (fun c => (2115764225-1+2*2^9*c.k,97206098825097+c.lower,97206477471724+c.upper)) = pointBounds16112 := by
 decide +kernel
def cuts16113 : List PrefixCut := [⟨64,409855196,409855458⟩,
⟨128,810386090,810386615⟩]
theorem checked16113 : checkPrefixCuts (2^48) 2115895297 9 Manual.Count131072.C016113.packed 128 cuts16113 = true := by
 decide +kernel
def pointBounds16113 : List (Nat × Nat × Nat) := [(2115960832,97207316189708,97207694837123)]
theorem point_links_checked16113 : (cuts16113.take 1).map (fun c => (2115895297-1+2*2^9*c.k,97206906334512+c.lower,97207284981665+c.upper)) = pointBounds16113 := by
 decide +kernel
def cuts16114 : List PrefixCut := [⟨1,6384982,6384987⟩,
⟨66,414751352,414751618⟩,
⟨128,814725230,814725755⟩]
theorem checked16114 : checkPrefixCuts (2^48) 2116026369 9 Manual.Count131072.C016114.packed 128 cuts16114 = true := by
 decide +kernel
def pointBounds16114 : List (Nat × Nat × Nat) := [(2116027392,97207723105584,97208101753267),(2116093952,97208131471954,97208510119898)]
theorem point_links_checked16114 : (cuts16114.take 2).map (fun c => (2116026369-1+2*2^9*c.k,97207716720602+c.lower,97208095368280+c.upper)) = pointBounds16114 := by
 decide +kernel
def cuts16115 : List PrefixCut := [⟨3,20217849,20217861⟩,
⟨68,430154534,430154809⟩,
⟨128,814674721,814675242⟩]
theorem checked16115 : checkPrefixCuts (2^48) 2116157441 9 Manual.Count131072.C016115.packed 128 cuts16115 = true := by
 decide +kernel
def pointBounds16115 : List (Nat × Nat × Nat) := [(2116160512,97208551663681,97208930311896),(2116227072,97208961600366,97209340248844)]
theorem point_links_checked16115 : (cuts16115.take 2).map (fun c => (2116157441-1+2*2^9*c.k,97208531445832+c.lower,97208910094035+c.upper)) = pointBounds16115 := by
 decide +kernel
def cuts16116 : List PrefixCut := [⟨5,33117964,33117984⟩,
⟨70,443028992,443029275⟩,
⟨128,817151355,817151878⟩]
theorem checked16116 : checkPrefixCuts (2^48) 2116288513 9 Manual.Count131072.C016116.packed 128 cuts16116 = true := by
 decide +kernel
def pointBounds16116 : List (Nat × Nat × Nat) := [(2116293632,97209379238517,97209757887261),(2116360192,97209789149545,97210167798552)]
theorem point_links_checked16116 : (cuts16116.take 2).map (fun c => (2116288513-1+2*2^9*c.k,97209346120553+c.lower,97209724769277+c.upper)) = pointBounds16116 := by
 decide +kernel
def cuts16117 : List PrefixCut := [⟨7,44420519,44420548⟩,
⟨72,459625554,459625847⟩,
⟨128,822420521,822421047⟩]
theorem checked16117 : checkPrefixCuts (2^48) 2116419585 9 Manual.Count131072.C016117.packed 128 cuts16117 = true := by
 decide +kernel
def pointBounds16117 : List (Nat × Nat × Nat) := [(2116426752,97210207692427,97210586341703),(2116493312,97210622897462,97211001547002)]
theorem point_links_checked16117 : (cuts16117.take 2).map (fun c => (2116419585-1+2*2^9*c.k,97210163271908+c.lower,97210541921155+c.upper)) = pointBounds16117 := by
 decide +kernel
def cuts16118 : List PrefixCut := [⟨9,56386598,56386635⟩,
⟨74,471698364,471698668⟩,
⟨128,806411702,806412217⟩]
theorem checked16118 : checkPrefixCuts (2^48) 2116550657 9 Manual.Count131072.C016118.packed 128 cuts16118 = true := by
 decide +kernel
def pointBounds16118 : List (Nat × Nat × Nat) := [(2116559872,97211042079027,97211420728837),(2116626432,97211457390793,97211836040870)]
theorem point_links_checked16118 : (cuts16118.take 2).map (fun c => (2116550657-1+2*2^9*c.k,97210985692429+c.lower,97211364342202+c.upper)) = pointBounds16118 := by
 decide +kernel
def cuts16119 : List PrefixCut := [⟨11,72340554,72340601⟩,
⟨76,481243332,481243638⟩,
⟨128,809686042,809686557⟩]
theorem checked16119 : checkPrefixCuts (2^48) 2116681729 9 Manual.Count131072.C016119.packed 128 cuts16119 = true := by
 decide +kernel
def pointBounds16119 : List (Nat × Nat × Nat) := [(2116692992,97211864444685,97212243095020),(2116759552,97212273347463,97212651998057)]
theorem point_links_checked16119 : (cuts16119.take 2).map (fun c => (2116681729-1+2*2^9*c.k,97211792104131+c.lower,97212170754419+c.upper)) = pointBounds16119 := by
 decide +kernel
def cuts16120 : List PrefixCut := [⟨13,85101226,85101277⟩,
⟨78,497701454,497701770⟩,
⟨128,813757961,813758482⟩]
theorem checked16120 : checkPrefixCuts (2^48) 2116812801 9 Manual.Count131072.C016120.packed 128 cuts16120 = true := by
 decide +kernel
def pointBounds16120 : List (Nat × Nat × Nat) := [(2116826112,97212686891399,97213065542253),(2116892672,97213099491627,97213478142746)]
theorem point_links_checked16120 : (cuts16120.take 2).map (fun c => (2116812801-1+2*2^9*c.k,97212601790173+c.lower,97212980440976+c.upper)) = pointBounds16120 := by
 decide +kernel
def cuts16121 : List PrefixCut := [⟨15,95599949,95600009⟩,
⟨80,505648001,505648321⟩,
⟨128,806793759,806794271⟩]
theorem checked16121 : checkPrefixCuts (2^48) 2116943873 9 Manual.Count131072.C016121.packed 128 cuts16121 = true := by
 decide +kernel
def pointBounds16121 : List (Nat × Nat × Nat) := [(2116959232,97213511148083,97213889799467),(2117025792,97213921196135,97214299847779)]
theorem point_links_checked16121 : (cuts16121.take 2).map (fun c => (2116943873-1+2*2^9*c.k,97213415548134+c.lower,97213794199458+c.upper)) = pointBounds16121 := by
 decide +kernel
def cuts16122 : List PrefixCut := [⟨17,107293936,107294006⟩,
⟨82,518778559,518778895⟩,
⟨128,804084637,804085157⟩]
theorem checked16122 : checkPrefixCuts (2^48) 2117074945 9 Manual.Count131072.C016122.packed 128 cuts16122 = true := by
 decide +kernel
def pointBounds16122 : List (Nat × Nat × Nat) := [(2117092352,97214329635829,97214708287735),(2117158912,97214741120452,97215119772624)]
theorem point_links_checked16122 : (cuts16122.take 2).map (fun c => (2117074945-1+2*2^9*c.k,97214222341893+c.lower,97214600993729+c.upper)) = pointBounds16122 := by
 decide +kernel
def cuts16123 : List PrefixCut := [⟨19,122443054,122443132⟩,
⟨84,537890230,537890571⟩,
⟨128,814005690,814006215⟩]
theorem checked16123 : checkPrefixCuts (2^48) 2117206017 9 Manual.Count131072.C016123.packed 128 cuts16123 = true := by
 decide +kernel
def pointBounds16123 : List (Nat × Nat × Nat) := [(2117225472,97215148869584,97215527522018),(2117292032,97215564316760,97215942969457)]
theorem point_links_checked16123 : (cuts16123.take 2).map (fun c => (2117206017-1+2*2^9*c.k,97215026426530+c.lower,97215405078886+c.upper)) = pointBounds16123 := by
 decide +kernel
def cuts16124 : List PrefixCut := [⟨21,130411676,130411760⟩,
⟨86,541312792,541313139⟩,
⟨128,809036371,809036887⟩]
theorem checked16124 : checkPrefixCuts (2^48) 2117337089 9 Manual.Count131072.C016124.packed 128 cuts16124 = true := by
 decide +kernel
def pointBounds16124 : List (Nat × Nat × Nat) := [(2117358592,97215970843896,97216349496861),(2117425152,97216381745012,97216760398240)]
theorem point_links_checked16124 : (cuts16124.take 2).map (fun c => (2117337089-1+2*2^9*c.k,97215840432220+c.lower,97216219085101+c.upper)) = pointBounds16124 := by
 decide +kernel
def cuts16125 : List PrefixCut := [⟨23,142500087,142500179⟩,
⟨88,551780410,551780760⟩,
⟨128,809119286,809119800⟩]
theorem checked16125 : checkPrefixCuts (2^48) 2117468161 9 Manual.Count131072.C016125.packed 128 cuts16125 = true := by
 decide +kernel
def pointBounds16125 : List (Nat × Nat × Nat) := [(2117491712,97216791968678,97217170622167),(2117558272,97217201249001,97217579902748)]
theorem point_links_checked16125 : (cuts16125.take 2).map (fun c => (2117468161-1+2*2^9*c.k,97216649468591+c.lower,97217028121988+c.upper)) = pointBounds16125 := by
 decide +kernel
def cuts16126 : List PrefixCut := [⟨25,156447907,156448007⟩,
⟨90,565037862,565038223⟩,
⟨128,807341406,807341919⟩]
theorem checked16126 : checkPrefixCuts (2^48) 2117599233 9 Manual.Count131072.C016126.packed 128 cuts16126 = true := by
 decide +kernel
def pointBounds16126 : List (Nat × Nat × Nat) := [(2117624832,97217615035784,97217993689795),(2117691392,97218023625739,97218402280011)]
theorem point_links_checked16126 : (cuts16126.take 2).map (fun c => (2117599233-1+2*2^9*c.k,97217458587877+c.lower,97217837241788+c.upper)) = pointBounds16126 := by
 decide +kernel
def cuts16127 : List PrefixCut := [⟨27,168666098,168666208⟩,
⟨92,582413746,582414120⟩,
⟨128,812607652,812608171⟩]
theorem checked16127 : checkPrefixCuts (2^48) 2117730305 9 Manual.Count131072.C016127.packed 128 cuts16127 = true := by
 decide +kernel
def pointBounds16127 : List (Nat × Nat × Nat) := [(2117757952,97218434595381,97218813249915),(2117824512,97218848343029,97219226997827)]
theorem point_links_checked16127 : (cuts16127.take 2).map (fun c => (2117730305-1+2*2^9*c.k,97218265929283+c.lower,97218644583707+c.upper)) = pointBounds16127 := by
 decide +kernel
def cuts16128 : List PrefixCut := [⟨29,186331865,186331982⟩,
⟨94,596731071,596731449⟩,
⟨128,816810327,816810849⟩]
theorem checked16128 : checkPrefixCuts (2^48) 2117861377 9 Manual.Count131072.C016128.packed 128 cuts16128 = true := by
 decide +kernel
def pointBounds16128 : List (Nat × Nat × Nat) := [(2117891072,97219264868800,97219643523860),(2117957632,97219675268006,97220053923327)]
theorem point_links_checked16128 : (cuts16128.take 2).map (fun c => (2117861377-1+2*2^9*c.k,97219078536935+c.lower,97219457191878+c.upper)) = pointBounds16128 := by
 decide +kernel
def cuts16129 : List PrefixCut := [⟨31,197350568,197350694⟩,
⟨96,613704145,613704535⟩,
⟨128,812507314,812507835⟩]
theorem checked16129 : checkPrefixCuts (2^48) 2117992449 9 Manual.Count131072.C016129.packed 128 cuts16129 = true := by
 decide +kernel
def pointBounds16129 : List (Nat × Nat × Nat) := [(2118024192,97220092697830,97220471353421),(2118090752,97220509051407,97220887707262)]
theorem point_links_checked16129 : (cuts16129.take 2).map (fun c => (2117992449-1+2*2^9*c.k,97219895347262+c.lower,97220274002727+c.upper)) = pointBounds16129 := by
 decide +kernel
def cuts16130 : List PrefixCut := [⟨33,207969313,207969447⟩,
⟨98,619247121,619247516⟩,
⟨128,814184329,814184852⟩]
theorem checked16130 : checkPrefixCuts (2^48) 2118123521 9 Manual.Count131072.C016130.packed 128 cuts16130 = true := by
 decide +kernel
def pointBounds16130 : List (Nat × Nat × Nat) := [(2118157312,97220915823889,97221294480009),(2118223872,97221327101697,97221705758078)]
theorem point_links_checked16130 : (cuts16130.take 2).map (fun c => (2118123521-1+2*2^9*c.k,97220707854576+c.lower,97221086510562+c.upper)) = pointBounds16130 := by
 decide +kernel
def cuts16131 : List PrefixCut := [⟨35,219251056,219251196⟩,
⟨100,625719563,625719963⟩,
⟨128,807357313,807357830⟩]
theorem checked16131 : checkPrefixCuts (2^48) 2118254593 9 Manual.Count131072.C016131.packed 128 cuts16131 = true := by
 decide +kernel
def pointBounds16131 : List (Nat × Nat × Nat) := [(2118290432,97221741289961,97222119946610),(2118356992,97222147758468,97222526415377)]
theorem point_links_checked16131 : (cuts16131.take 2).map (fun c => (2118254593-1+2*2^9*c.k,97221522038905+c.lower,97221900695414+c.upper)) = pointBounds16131 := by
 decide +kernel
def cuts16132 : List PrefixCut := [⟨37,232923127,232923279⟩,
⟨102,651324088,651324513⟩,
⟨128,816873836,816874370⟩]
theorem checked16132 : checkPrefixCuts (2^48) 2118385665 9 Manual.Count131072.C016132.packed 128 cuts16132 = true := by
 decide +kernel
def pointBounds16132 : List (Nat × Nat × Nat) := [(2118423552,97222562319345,97222940976523),(2118490112,97222980720306,97223359377757)]
theorem point_links_checked16132 : (cuts16132.take 2).map (fun c => (2118385665-1+2*2^9*c.k,97222329396218+c.lower,97222708053244+c.upper)) = pointBounds16132 := by
 decide +kernel
def cuts16133 : List PrefixCut := [⟨39,249250788,249250944⟩,
⟨104,653276591,653277010⟩,
⟨128,805397502,805398017⟩]
theorem checked16133 : checkPrefixCuts (2^48) 2118516737 9 Manual.Count131072.C016133.packed 128 cuts16133 = true := by
 decide +kernel
def pointBounds16133 : List (Nat × Nat × Nat) := [(2118556672,97223395520842,97223774178558),(2118623232,97223799546645,97224178204624)]
theorem point_links_checked16133 : (cuts16133.take 2).map (fun c => (2118516737-1+2*2^9*c.k,97223146270054+c.lower,97223524927614+c.upper)) = pointBounds16133 := by
 decide +kernel
def cuts16134 : List PrefixCut := [⟨41,252822330,252822493⟩,
⟨106,669709365,669709798⟩,
⟨128,803753394,803753913⟩]
theorem checked16134 : checkPrefixCuts (2^48) 2118647809 9 Manual.Count131072.C016134.packed 128 cuts16134 = true := by
 decide +kernel
def pointBounds16134 : List (Nat × Nat × Nat) := [(2118689792,97224204489886,97224583148124),(2118756352,97224621376921,97225000035429)]
theorem point_links_checked16134 : (cuts16134.take 2).map (fun c => (2118647809-1+2*2^9*c.k,97223951667556+c.lower,97224330325631+c.upper)) = pointBounds16134 := by
 decide +kernel
def cuts16135 : List PrefixCut := [⟨43,272069253,272069428⟩,
⟨108,677505673,677506105⟩,
⟨128,805032189,805032703⟩]
theorem checked16135 : checkPrefixCuts (2^48) 2118778881 9 Manual.Count131072.C016135.packed 128 cuts16135 = true := by
 decide +kernel
def pointBounds16135 : List (Nat × Nat × Nat) := [(2118822912,97225027490203,97225406148972),(2118889472,97225432926623,97225811585649)]
theorem point_links_checked16135 : (cuts16135.take 2).map (fun c => (2118778881-1+2*2^9*c.k,97224755420950+c.lower,97225134079544+c.upper)) = pointBounds16135 := by
 decide +kernel
def cuts16136 : List PrefixCut := [⟨45,289321270,289321452⟩,
⟨110,698318715,698319154⟩,
⟨128,809897449,809897961⟩]
theorem checked16136 : checkPrefixCuts (2^48) 2118909953 9 Manual.Count131072.C016136.packed 128 cuts16136 = true := by
 decide +kernel
def pointBounds16136 : List (Nat × Nat × Nat) := [(2118956032,97225849774409,97226228433699),(2119022592,97226258771854,97226637431401)]
theorem point_links_checked16136 : (cuts16136.take 2).map (fun c => (2118909953-1+2*2^9*c.k,97225560453139+c.lower,97225939112247+c.upper)) = pointBounds16136 := by
 decide +kernel
def cuts16137 : List PrefixCut := [⟨47,296343172,296343359⟩,
⟨112,710362321,710362765⟩,
⟨128,810245635,810246143⟩]
theorem checked16137 : checkPrefixCuts (2^48) 2119041025 9 Manual.Count131072.C016137.packed 128 cuts16137 = true := by
 decide +kernel
def pointBounds16137 : List (Nat × Nat × Nat) := [(2119089152,97226666693760,97227045353567),(2119155712,97227080712909,97227459372973)]
theorem point_links_checked16137 : (cuts16137.take 2).map (fun c => (2119041025-1+2*2^9*c.k,97226370350588+c.lower,97226749010208+c.upper)) = pointBounds16137 := by
 decide +kernel
def cuts16138 : List PrefixCut := [⟨49,312263260,312263460⟩,
⟨114,728381460,728381928⟩,
⟨128,818563023,818563549⟩]
theorem checked16138 : checkPrefixCuts (2^48) 2119172097 9 Manual.Count131072.C016138.packed 128 cuts16138 = true := by
 decide +kernel
def pointBounds16138 : List (Nat × Nat × Nat) := [(2119222272,97227492859483,97227871519811),(2119288832,97227908977683,97228287638279)]
theorem point_links_checked16138 : (cuts16138.take 2).map (fun c => (2119172097-1+2*2^9*c.k,97227180596223+c.lower,97227559256351+c.upper)) = pointBounds16138 := by
 decide +kernel
def cuts16139 : List PrefixCut := [⟨51,323798599,323798806⟩,
⟨116,725945630,725946097⟩,
⟨128,803504916,803505433⟩]
theorem checked16139 : checkPrefixCuts (2^48) 2119303169 9 Manual.Count131072.C016139.packed 128 cuts16139 = true := by
 decide +kernel
def pointBounds16139 : List (Nat × Nat × Nat) := [(2119355392,97228322957845,97228701618706),(2119421952,97228725104876,97229103765997)]
theorem point_links_checked16139 : (cuts16139.take 2).map (fun c => (2119303169-1+2*2^9*c.k,97227999159246+c.lower,97228377819900+c.upper)) = pointBounds16139 := by
 decide +kernel
def cuts16140 : List PrefixCut := [⟨53,345027174,345027391⟩,
⟨118,758038748,758039227⟩,
⟨128,821250941,821251459⟩]
theorem checked16140 : checkPrefixCuts (2^48) 2119434241 9 Manual.Count131072.C016140.packed 128 cuts16140 = true := by
 decide +kernel
def pointBounds16140 : List (Nat × Nat × Nat) := [(2119488512,97229147691336,97229526352724),(2119555072,97229560702910,97229939364560)]
theorem point_links_checked16140 : (cuts16140.take 2).map (fun c => (2119434241-1+2*2^9*c.k,97228802664162+c.lower,97229181325333+c.upper)) = pointBounds16140 := by
 decide +kernel
def cuts16141 : List PrefixCut := [⟨55,349786335,349786554⟩,
⟨120,762240745,762241228⟩,
⟨128,812169950,812170466⟩]
theorem checked16141 : checkPrefixCuts (2^48) 2119565313 9 Manual.Count131072.C016141.packed 128 cuts16141 = true := by
 decide +kernel
def pointBounds16141 : List (Nat × Nat × Nat) := [(2119621632,97229973701438,97230352363346),(2119688192,97230386155848,97230764818020)]
theorem point_links_checked16141 : (cuts16141.take 2).map (fun c => (2119565313-1+2*2^9*c.k,97229623915103+c.lower,97230002576792+c.upper)) = pointBounds16141 := by
 decide +kernel
def cuts16142 : List PrefixCut := [⟨57,359856394,359856625⟩,
⟨122,771886568,771887056⟩,
⟨128,809729487,809729998⟩]
theorem checked16142 : checkPrefixCuts (2^48) 2119696385 9 Manual.Count131072.C016142.packed 128 cuts16142 = true := by
 decide +kernel
def pointBounds16142 : List (Nat × Nat × Nat) := [(2119754752,97230795941447,97231174603883),(2119821312,97231207971621,97231586634314)]
theorem point_links_checked16142 : (cuts16142.take 2).map (fun c => (2119696385-1+2*2^9*c.k,97230436085053+c.lower,97230814747258+c.upper)) = pointBounds16142 := by
 decide +kernel
def cuts16143 : List PrefixCut := [⟨59,375103757,375103994⟩,
⟨124,793215835,793216339⟩,
⟨128,818841198,818841719⟩]
theorem checked16143 : checkPrefixCuts (2^48) 2119827457 9 Manual.Count131072.C016143.packed 128 cuts16143 = true := by
 decide +kernel
def pointBounds16143 : List (Nat × Nat × Nat) := [(2119887872,97231620918297,97231999581250),(2119954432,97232039030375,97232417693595)]
theorem point_links_checked16143 : (cuts16143.take 2).map (fun c => (2119827457-1+2*2^9*c.k,97231245814540+c.lower,97231624477256+c.upper)) = pointBounds16143 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000191
