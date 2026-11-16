import PlattAssemblyKernel
import PlattCertificates.Count131072.C024096
import PlattCertificates.Count131072.C024097
import PlattCertificates.Count131072.C024098
import PlattCertificates.Count131072.C024099
import PlattCertificates.Count131072.C024100
import PlattCertificates.Count131072.C024101
import PlattCertificates.Count131072.C024102
import PlattCertificates.Count131072.C024103
import PlattCertificates.Count131072.C024104
import PlattCertificates.Count131072.C024105
import PlattCertificates.Count131072.C024106
import PlattCertificates.Count131072.C024107
import PlattCertificates.Count131072.C024108
import PlattCertificates.Count131072.C024109
import PlattCertificates.Count131072.C024110
import PlattCertificates.Count131072.C024111
import PlattCertificates.Count131072.C024112
import PlattCertificates.Count131072.C024113
import PlattCertificates.Count131072.C024114
import PlattCertificates.Count131072.C024115
import PlattCertificates.Count131072.C024116
import PlattCertificates.Count131072.C024117
import PlattCertificates.Count131072.C024118
import PlattCertificates.Count131072.C024119
import PlattCertificates.Count131072.C024120
import PlattCertificates.Count131072.C024121
import PlattCertificates.Count131072.C024122
import PlattCertificates.Count131072.C024123
import PlattCertificates.Count131072.C024124
import PlattCertificates.Count131072.C024125
import PlattCertificates.Count131072.C024126
import PlattCertificates.Count131072.C024127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000128
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24096 : List PrefixCut := [⟨4,16645075,16645084⟩,
⟨101,421460918,421461159⟩,
⟨128,536459056,536459365⟩]
theorem checked24096 : checkPrefixCuts (2^48) 3162243073 9 Manual.Count131072.C024096.packed 128 cuts24096 = true := by
 decide +kernel
def pointBounds24096 : List (Nat × Nat × Nat) := [(3162247168,102425134126079,102425515876250),(3162346496,102425538941922,102425920692325)]
theorem point_links_checked24096 : (cuts24096.take 2).map (fun c => (3162243073-1+2*2^9*c.k,102425117481004+c.lower,102425499231166+c.upper)) = pointBounds24096 := by
 decide +kernel
def cuts24097 : List PrefixCut := [⟨70,290072024,290072185⟩,
⟨128,527447325,527447621⟩]
theorem checked24097 : checkPrefixCuts (2^48) 3162374145 9 Manual.Count131072.C024097.packed 128 cuts24097 = true := by
 decide +kernel
def pointBounds24097 : List (Nat × Nat × Nat) := [(3162445824,102425944012084,102426325762716)]
theorem point_links_checked24097 : (cuts24097.take 1).map (fun c => (3162374145-1+2*2^9*c.k,102425653940060+c.lower,102426035690531+c.upper)) = pointBounds24097 := by
 decide +kernel
def cuts24098 : List PrefixCut := [⟨39,161184808,161184898⟩,
⟨128,535791559,535791862⟩]
theorem checked24098 : checkPrefixCuts (2^48) 3162505217 9 Manual.Count131072.C024098.packed 128 cuts24098 = true := by
 decide +kernel
def pointBounds24098 : List (Nat × Nat × Nat) := [(3162545152,102426342572193,102426724323050)]
theorem point_links_checked24098 : (cuts24098.take 1).map (fun c => (3162505217-1+2*2^9*c.k,102426181387385+c.lower,102426563138152+c.upper)) = pointBounds24098 := by
 decide +kernel
def cuts24099 : List PrefixCut := [⟨8,31861989,31862007⟩,
⟨105,429685088,429685341⟩,
⟨128,524733583,524733889⟩]
theorem checked24099 : checkPrefixCuts (2^48) 3162636289 9 Manual.Count131072.C024099.packed 128 cuts24099 = true := by
 decide +kernel
def pointBounds24099 : List (Nat × Nat × Nat) := [(3162644480,102426749040933,102427130792021),(3162743808,102427146864032,102427528615355)]
theorem point_links_checked24099 : (cuts24099.take 2).map (fun c => (3162636289-1+2*2^9*c.k,102426717178944+c.lower,102427098930014+c.upper)) = pointBounds24099 := by
 decide +kernel
def cuts24100 : List PrefixCut := [⟨74,308991756,308991932⟩,
⟨128,530585554,530585858⟩]
theorem checked24100 : checkPrefixCuts (2^48) 3162767361 9 Manual.Count131072.C024100.packed 128 cuts24100 = true := by
 decide +kernel
def pointBounds24100 : List (Nat × Nat × Nat) := [(3162843136,102427550904283,102427932655835)]
theorem point_links_checked24100 : (cuts24100.take 1).map (fun c => (3162767361-1+2*2^9*c.k,102427241912527+c.lower,102427623663903+c.upper)) = pointBounds24100 := by
 decide +kernel
def cuts24101 : List PrefixCut := [⟨43,180386975,180387080⟩,
⟨128,542755237,542755546⟩]
theorem checked24101 : checkPrefixCuts (2^48) 3162898433 9 Manual.Count131072.C024101.packed 128 cuts24101 = true := by
 decide +kernel
def pointBounds24101 : List (Nat × Nat × Nat) := [(3162942464,102427952885056,102428334636841)]
theorem point_links_checked24101 : (cuts24101.take 1).map (fun c => (3162898433-1+2*2^9*c.k,102427772498081+c.lower,102428154249761+c.upper)) = pointBounds24101 := by
 decide +kernel
def cuts24102 : List PrefixCut := [⟨12,49477793,49477822⟩,
⟨109,454014000,454014253⟩,
⟨128,535168868,535169166⟩]
theorem checked24102 : checkPrefixCuts (2^48) 3163029505 9 Manual.Count131072.C024102.packed 128 cuts24102 = true := by
 decide +kernel
def pointBounds24102 : List (Nat × Nat × Nat) := [(3163041792,102428364731111,102428746483129),(3163141120,102428769267318,102429151019560)]
theorem point_links_checked24102 : (cuts24102.take 2).map (fun c => (3163029505-1+2*2^9*c.k,102428315253318+c.lower,102428697005307+c.upper)) = pointBounds24102 := by
 decide +kernel
def cuts24103 : List PrefixCut := [⟨78,327372918,327373105⟩,
⟨128,531053572,531053875⟩]
theorem checked24103 : checkPrefixCuts (2^48) 3163160577 9 Manual.Count131072.C024103.packed 128 cuts24103 = true := by
 decide +kernel
def pointBounds24103 : List (Nat × Nat × Nat) := [(3163240448,102429177795104,102429559547578)]
theorem point_links_checked24103 : (cuts24103.take 1).map (fun c => (3163160577-1+2*2^9*c.k,102428850422186+c.lower,102429232174473+c.upper)) = pointBounds24103 := by
 decide +kernel
def cuts24104 : List PrefixCut := [⟨47,192999730,192999840⟩,
⟨128,529963664,529963967⟩]
theorem checked24104 : checkPrefixCuts (2^48) 3163291649 9 Manual.Count131072.C024104.packed 128 cuts24104 = true := by
 decide +kernel
def pointBounds24104 : List (Nat × Nat × Nat) := [(3163339776,102429574475488,102429956228188)]
theorem point_links_checked24104 : (cuts24104.take 1).map (fun c => (3163291649-1+2*2^9*c.k,102429381475758+c.lower,102429763228348+c.upper)) = pointBounds24104 := by
 decide +kernel
def cuts24105 : List PrefixCut := [⟨16,65576587,65576624⟩,
⟨113,472197362,472197628⟩,
⟨128,532877961,532878261⟩]
theorem checked24105 : checkPrefixCuts (2^48) 3163422721 9 Manual.Count131072.C024105.packed 128 cuts24105 = true := by
 decide +kernel
def pointBounds24105 : List (Nat × Nat × Nat) := [(3163439104,102429977016009,102430358768939),(3163538432,102430383636784,102430765389943)]
theorem point_links_checked24105 : (cuts24105.take 2).map (fun c => (3163422721-1+2*2^9*c.k,102429911439422+c.lower,102430293192315+c.upper)) = pointBounds24105 := by
 decide +kernel
def cuts24106 : List PrefixCut := [⟨82,342991210,342991405⟩,
⟨128,533122748,533123053⟩]
theorem checked24106 : checkPrefixCuts (2^48) 3163553793 9 Manual.Count131072.C024106.packed 128 cuts24106 = true := by
 decide +kernel
def pointBounds24106 : List (Nat × Nat × Nat) := [(3163637760,102430787308593,102431169061981)]
theorem point_links_checked24106 : (cuts24106.take 1).map (fun c => (3163553793-1+2*2^9*c.k,102430444317383+c.lower,102430826070576+c.upper)) = pointBounds24106 := by
 decide +kernel
def cuts24107 : List PrefixCut := [⟨51,214951200,214951319⟩,
⟨128,532833934,532834234⟩]
theorem checked24107 : checkPrefixCuts (2^48) 3163684865 9 Manual.Count131072.C024107.packed 128 cuts24107 = true := by
 decide +kernel
def pointBounds24107 : List (Nat × Nat × Nat) := [(3163737088,102431192391331,102431574144948)]
theorem point_links_checked24107 : (cuts24107.take 1).map (fun c => (3163684865-1+2*2^9*c.k,102430977440131+c.lower,102431359193629+c.upper)) = pointBounds24107 := by
 decide +kernel
def cuts24108 : List PrefixCut := [⟨20,86475547,86475597⟩,
⟨117,491532839,491533117⟩,
⟨128,537171050,537171354⟩]
theorem checked24108 : checkPrefixCuts (2^48) 3163815937 9 Manual.Count131072.C024108.packed 128 cuts24108 = true := by
 decide +kernel
def pointBounds24108 : List (Nat × Nat × Nat) := [(3163836416,102431596749612,102431978503460),(3163935744,102432001806904,102432383560980)]
theorem point_links_checked24108 : (cuts24108.take 2).map (fun c => (3163815937-1+2*2^9*c.k,102431510274065+c.lower,102431892027863+c.upper)) = pointBounds24108 := by
 decide +kernel
def cuts24109 : List PrefixCut := [⟨86,356737555,356737754⟩,
⟨128,530743588,530743883⟩]
theorem checked24109 : checkPrefixCuts (2^48) 3163947009 9 Manual.Count131072.C024109.packed 128 cuts24109 = true := by
 decide +kernel
def pointBounds24109 : List (Nat × Nat × Nat) := [(3164035072,102432404182670,102432785936971)]
theorem point_links_checked24109 : (cuts24109.take 1).map (fun c => (3163947009-1+2*2^9*c.k,102432047445115+c.lower,102432429199217+c.upper)) = pointBounds24109 := by
 decide +kernel
def cuts24110 : List PrefixCut := [⟨55,234317343,234317473⟩,
⟨128,545221650,545221950⟩]
theorem checked24110 : checkPrefixCuts (2^48) 3164078081 9 Manual.Count131072.C024110.packed 128 cuts24110 = true := by
 decide +kernel
def pointBounds24110 : List (Nat × Nat × Nat) := [(3164134400,102432812506046,102433194260573)]
theorem point_links_checked24110 : (cuts24110.take 1).map (fun c => (3164078081-1+2*2^9*c.k,102432578188703+c.lower,102432959943100+c.upper)) = pointBounds24110 := by
 decide +kernel
def cuts24111 : List PrefixCut := [⟨24,98651649,98651708⟩,
⟨121,499032497,499032791⟩,
⟨128,527586172,527586484⟩]
theorem checked24111 : checkPrefixCuts (2^48) 3164209153 9 Manual.Count131072.C024111.packed 128 cuts24111 = true := by
 decide +kernel
def pointBounds24111 : List (Nat × Nat × Nat) := [(3164233728,102433222062002,102433603816758),(3164333056,102433622442850,102434004197841)]
theorem point_links_checked24111 : (cuts24111.take 2).map (fun c => (3164209153-1+2*2^9*c.k,102433123410353+c.lower,102433505165050+c.upper)) = pointBounds24111 := by
 decide +kernel
def cuts24112 : List PrefixCut := [⟨90,379998133,379998347⟩,
⟨128,535925749,535926050⟩]
theorem checked24112 : checkPrefixCuts (2^48) 3164340225 9 Manual.Count131072.C024112.packed 128 cuts24112 = true := by
 decide +kernel
def pointBounds24112 : List (Nat × Nat × Nat) := [(3164432384,102434030994658,102434412749881)]
theorem point_links_checked24112 : (cuts24112.take 1).map (fun c => (3164340225-1+2*2^9*c.k,102433650996525+c.lower,102434032751534+c.upper)) = pointBounds24112 := by
 decide +kernel
def cuts24113 : List PrefixCut := [⟨59,245139678,245139817⟩,
⟨128,526030446,526030746⟩]
theorem checked24113 : checkPrefixCuts (2^48) 3164471297 9 Manual.Count131072.C024113.packed 128 cuts24113 = true := by
 decide +kernel
def pointBounds24113 : List (Nat × Nat × Nat) := [(3164531712,102434432061952,102434813817401)]
theorem point_links_checked24113 : (cuts24113.take 1).map (fun c => (3164471297-1+2*2^9*c.k,102434186922274+c.lower,102434568677584+c.upper)) = pointBounds24113 := by
 decide +kernel
def cuts24114 : List PrefixCut := [⟨28,117584469,117584537⟩,
⟨125,519871843,519872136⟩,
⟨128,532145722,532146021⟩]
theorem checked24114 : checkPrefixCuts (2^48) 3164602369 9 Manual.Count131072.C024114.packed 128 cuts24114 = true := by
 decide +kernel
def pointBounds24114 : List (Nat × Nat × Nat) := [(3164631040,102434830537189,102435212292867),(3164730368,102435232824563,102435614580466)]
theorem point_links_checked24114 : (cuts24114.take 2).map (fun c => (3164602369-1+2*2^9*c.k,102434712952720+c.lower,102435094708330+c.upper)) = pointBounds24114 := by
 decide +kernel
def cuts24115 : List PrefixCut := [⟨94,396226590,396226815⟩,
⟨128,537726807,537727114⟩]
theorem checked24115 : checkPrefixCuts (2^48) 3164733441 9 Manual.Count131072.C024115.packed 128 cuts24115 = true := by
 decide +kernel
def pointBounds24115 : List (Nat × Nat × Nat) := [(3164829696,102435641325032,102436023081166)]
theorem point_links_checked24115 : (cuts24115.take 1).map (fun c => (3164733441-1+2*2^9*c.k,102435245098442+c.lower,102435626854351+c.upper)) = pointBounds24115 := by
 decide +kernel
def cuts24116 : List PrefixCut := [⟨63,264052534,264052685⟩,
⟨128,536815198,536815500⟩]
theorem checked24116 : checkPrefixCuts (2^48) 3164864513 9 Manual.Count131072.C024116.packed 128 cuts24116 = true := by
 decide +kernel
def pointBounds24116 : List (Nat × Nat × Nat) := [(3164929024,102436046877783,102436428634150)]
theorem point_links_checked24116 : (cuts24116.take 1).map (fun c => (3164864513-1+2*2^9*c.k,102435782825249+c.lower,102436164581465+c.upper)) = pointBounds24116 := by
 decide +kernel
def cuts24117 : List PrefixCut := [⟨32,134111391,134111468⟩,
⟨128,534302922,534303230⟩]
theorem checked24117 : checkPrefixCuts (2^48) 3164995585 9 Manual.Count131072.C024117.packed 128 cuts24117 = true := by
 decide +kernel
def pointBounds24117 : List (Nat × Nat × Nat) := [(3165028352,102436453751838,102436835508433)]
theorem point_links_checked24117 : (cuts24117.take 1).map (fun c => (3164995585-1+2*2^9*c.k,102436319640447+c.lower,102436701396965+c.upper)) = pointBounds24117 := by
 decide +kernel
def cuts24118 : List PrefixCut := [⟨1,4090782,4090784⟩,
⟨98,410494651,410494877⟩,
⟨128,534547545,534547840⟩]
theorem checked24118 : checkPrefixCuts (2^48) 3165126657 9 Manual.Count131072.C024118.packed 128 cuts24118 = true := by
 decide +kernel
def pointBounds24118 : List (Nat × Nat × Nat) := [(3165127680,102436858034151,102437239790979),(3165227008,102437264438020,102437646195072)]
theorem point_links_checked24118 : (cuts24118.take 2).map (fun c => (3165126657-1+2*2^9*c.k,102436853943369+c.lower,102437235700195+c.upper)) = pointBounds24118 := by
 decide +kernel
def cuts24119 : List PrefixCut := [⟨67,281893552,281893711⟩,
⟨128,538615919,538616217⟩]
theorem checked24119 : checkPrefixCuts (2^48) 3165257729 9 Manual.Count131072.C024119.packed 128 cuts24119 = true := by
 decide +kernel
def pointBounds24119 : List (Nat × Nat × Nat) := [(3165326336,102437670384466,102438052141746)]
theorem point_links_checked24119 : (cuts24119.take 1).map (fun c => (3165257729-1+2*2^9*c.k,102437388490914+c.lower,102437770248035+c.upper)) = pointBounds24119 := by
 decide +kernel
def cuts24120 : List PrefixCut := [⟨36,154013208,154013291⟩,
⟨128,534858951,534859250⟩]
theorem checked24120 : checkPrefixCuts (2^48) 3165388801 9 Manual.Count131072.C024120.packed 128 cuts24120 = true := by
 decide +kernel
def pointBounds24120 : List (Nat × Nat × Nat) := [(3165425664,102438081120041,102438462877543)]
theorem point_links_checked24120 : (cuts24120.take 1).map (fun c => (3165388801-1+2*2^9*c.k,102437927106833+c.lower,102438308864252+c.upper)) = pointBounds24120 := by
 decide +kernel
def cuts24121 : List PrefixCut := [⟨5,22674330,22674342⟩,
⟨102,425114764,425115003⟩,
⟨128,534036498,534036796⟩]
theorem checked24121 : checkPrefixCuts (2^48) 3165519873 9 Manual.Count131072.C024121.packed 128 cuts24121 = true := by
 decide +kernel
def pointBounds24121 : List (Nat × Nat × Nat) := [(3165524992,102438484640114,102438866397844),(3165624320,102438887080548,102439268838505)]
theorem point_links_checked24121 : (cuts24121.take 2).map (fun c => (3165519873-1+2*2^9*c.k,102438461965784+c.lower,102438843723502+c.upper)) = pointBounds24121 := by
 decide +kernel
def cuts24122 : List PrefixCut := [⟨71,295729029,295729202⟩,
⟨128,533569929,533570232⟩]
theorem checked24122 : checkPrefixCuts (2^48) 3165650945 9 Manual.Count131072.C024122.packed 128 cuts24122 = true := by
 decide +kernel
def pointBounds24122 : List (Nat × Nat × Nat) := [(3165723648,102439291731311,102439673489500)]
theorem point_links_checked24122 : (cuts24122.take 1).map (fun c => (3165650945-1+2*2^9*c.k,102438996002282+c.lower,102439377760298+c.upper)) = pointBounds24122 := by
 decide +kernel
def cuts24123 : List PrefixCut := [⟨40,163596384,163596478⟩,
⟨128,535237022,535237317⟩]
theorem checked24123 : checkPrefixCuts (2^48) 3165782017 9 Manual.Count131072.C024123.packed 128 cuts24123 = true := by
 decide +kernel
def pointBounds24123 : List (Nat × Nat × Nat) := [(3165822976,102439693168595,102440074927008)]
theorem point_links_checked24123 : (cuts24123.take 1).map (fun c => (3165782017-1+2*2^9*c.k,102439529572211+c.lower,102439911330530+c.upper)) = pointBounds24123 := by
 decide +kernel
def cuts24124 : List PrefixCut := [⟨9,40275252,40275274⟩,
⟨106,447999583,447999841⟩,
⟨128,537259811,537260122⟩]
theorem checked24124 : checkPrefixCuts (2^48) 3165913089 9 Manual.Count131072.C024124.packed 128 cuts24124 = true := by
 decide +kernel
def pointBounds24124 : List (Nat × Nat × Nat) := [(3165922304,102440105084485,102440486843121),(3166021632,102440512808816,102440894567688)]
theorem point_links_checked24124 : (cuts24124.take 2).map (fun c => (3165913089-1+2*2^9*c.k,102440064809233+c.lower,102440446567847+c.upper)) = pointBounds24124 := by
 decide +kernel
def cuts24125 : List PrefixCut := [⟨75,317206669,317206843⟩,
⟨128,537859877,537860172⟩]
theorem checked24125 : checkPrefixCuts (2^48) 3166044161 9 Manual.Count131072.C024125.packed 128 cuts24125 = true := by
 decide +kernel
def pointBounds24125 : List (Nat × Nat × Nat) := [(3166120960,102440919275713,102441301034812)]
theorem point_links_checked24125 : (cuts24125.take 1).map (fun c => (3166044161-1+2*2^9*c.k,102440602069044+c.lower,102440983827969+c.upper)) = pointBounds24125 := by
 decide +kernel
def cuts24126 : List PrefixCut := [⟨44,177444365,177444468⟩,
⟨128,526547314,526547615⟩]
theorem checked24126 : checkPrefixCuts (2^48) 3166175233 9 Manual.Count131072.C024126.packed 128 cuts24126 = true := by
 decide +kernel
def pointBounds24126 : List (Nat × Nat × Nat) := [(3166220288,102441317373286,102441699132609)]
theorem point_links_checked24126 : (cuts24126.take 1).map (fun c => (3166175233-1+2*2^9*c.k,102441139928921+c.lower,102441521688141+c.upper)) = pointBounds24126 := by
 decide +kernel
def cuts24127 : List PrefixCut := [⟨13,57782879,57782908⟩,
⟨110,460389006,460389269⟩,
⟨128,536126274,536126581⟩]
theorem checked24127 : checkPrefixCuts (2^48) 3166306305 9 Manual.Count131072.C024127.packed 128 cuts24127 = true := by
 decide +kernel
def pointBounds24127 : List (Nat × Nat × Nat) := [(3166319616,102441724259114,102442106018664),(3166418944,102442126865241,102442508625025)]
theorem point_links_checked24127 : (cuts24127.take 2).map (fun c => (3166306305-1+2*2^9*c.k,102441666476235+c.lower,102442048235756+c.upper)) = pointBounds24127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000128
