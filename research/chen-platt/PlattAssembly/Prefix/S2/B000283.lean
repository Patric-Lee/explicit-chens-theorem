import PlattAssemblyKernel
import PlattCertificates.Count131072.C019056
import PlattCertificates.Count131072.C019057
import PlattCertificates.Count131072.C019058
import PlattCertificates.Count131072.C019059
import PlattCertificates.Count131072.C019060
import PlattCertificates.Count131072.C019061
import PlattCertificates.Count131072.C019062
import PlattCertificates.Count131072.C019063
import PlattCertificates.Count131072.C019064
import PlattCertificates.Count131072.C019065
import PlattCertificates.Count131072.C019066
import PlattCertificates.Count131072.C019067
import PlattCertificates.Count131072.C019068
import PlattCertificates.Count131072.C019069
import PlattCertificates.Count131072.C019070
import PlattCertificates.Count131072.C019071
import PlattCertificates.Count131072.C019072
import PlattCertificates.Count131072.C019073
import PlattCertificates.Count131072.C019074
import PlattCertificates.Count131072.C019075
import PlattCertificates.Count131072.C019076
import PlattCertificates.Count131072.C019077
import PlattCertificates.Count131072.C019078
import PlattCertificates.Count131072.C019079
import PlattCertificates.Count131072.C019080
import PlattCertificates.Count131072.C019081
import PlattCertificates.Count131072.C019082
import PlattCertificates.Count131072.C019083
import PlattCertificates.Count131072.C019084
import PlattCertificates.Count131072.C019085
import PlattCertificates.Count131072.C019086
import PlattCertificates.Count131072.C019087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000283
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19056 : List PrefixCut := [⟨41,225367935,225368068⟩,
⟨118,634575872,634576256⟩,
⟨128,690268557,690268972⟩]
theorem checked19056 : checkPrefixCuts (2^48) 2501640193 9 Manual.Count131072.C019056.packed 128 cuts19056 = true := by
 decide +kernel
def pointBounds19056 : List (Nat × Nat × Nat) := [(2501682176,99393691792625,99394071790715),(2501761024,99394101000562,99394480998903)]
theorem point_links_checked19056 : (cuts19056.take 2).map (fun c => (2501640193-1+2*2^9*c.k,99393466424690+c.lower,99393846422647+c.upper)) = pointBounds19056 := by
 decide +kernel
def cuts19057 : List PrefixCut := [⟨67,356765168,356765382⟩,
⟨128,675718955,675719362⟩]
theorem checked19057 : checkPrefixCuts (2^48) 2501771265 9 Manual.Count131072.C019057.packed 128 cuts19057 = true := by
 decide +kernel
def pointBounds19057 : List (Nat × Nat × Nat) := [(2501839872,99394513458415,99394893457001)]
theorem point_links_checked19057 : (cuts19057.take 1).map (fun c => (2501771265-1+2*2^9*c.k,99394156693247+c.lower,99394536691619+c.upper)) = pointBounds19057 := by
 decide +kernel
def cuts19058 : List PrefixCut := [⟨16,84377977,84378025⟩,
⟨93,492759643,492759933⟩,
⟨128,678720926,678721327⟩]
theorem checked19058 : checkPrefixCuts (2^48) 2501902337 9 Manual.Count131072.C019058.packed 128 cuts19058 = true := by
 decide +kernel
def pointBounds19058 : List (Nat × Nat × Nat) := [(2501918720,99394916790179,99395296789006),(2501997568,99395325171845,99395705170914)]
theorem point_links_checked19058 : (cuts19058.take 2).map (fun c => (2501902337-1+2*2^9*c.k,99394832412202+c.lower,99395212410981+c.upper)) = pointBounds19058 := by
 decide +kernel
def cuts19059 : List PrefixCut := [⟨42,225332473,225332605⟩,
⟨119,638975683,638976056⟩,
⟨128,689034964,689035365⟩]
theorem checked19059 : checkPrefixCuts (2^48) 2502033409 9 Manual.Count131072.C019059.packed 128 cuts19059 = true := by
 decide +kernel
def pointBounds19059 : List (Nat × Nat × Nat) := [(2502076416,99395736465601,99396116464913),(2502155264,99396150108811,99396530108364)]
theorem point_links_checked19059 : (cuts19059.take 2).map (fun c => (2502033409-1+2*2^9*c.k,99395511133128+c.lower,99395891132308+c.upper)) = pointBounds19059 := by
 decide +kernel
def cuts19060 : List PrefixCut := [⟨68,354571569,354571781⟩,
⟨128,668300771,668301174⟩]
theorem checked19060 : checkPrefixCuts (2^48) 2502164481 9 Manual.Count131072.C019060.packed 128 cuts19060 = true := by
 decide +kernel
def pointBounds19060 : List (Nat × Nat × Nat) := [(2502234112,99396554739661,99396934739454)]
theorem point_links_checked19060 : (cuts19060.take 1).map (fun c => (2502164481-1+2*2^9*c.k,99396200168092+c.lower,99396580167673+c.upper)) = pointBounds19060 := by
 decide +kernel
def cuts19061 : List PrefixCut := [⟨17,90776420,90776476⟩,
⟨94,504043007,504043309⟩,
⟨128,683676046,683676453⟩]
theorem checked19061 : checkPrefixCuts (2^48) 2502295553 9 Manual.Count131072.C019061.packed 128 cuts19061 = true := by
 decide +kernel
def pointBounds19061 : List (Nat × Nat × Nat) := [(2502312960,99396959245283,99397339245323),(2502391808,99397372511870,99397752512156)]
theorem point_links_checked19061 : (cuts19061.take 2).map (fun c => (2502295553-1+2*2^9*c.k,99396868468863+c.lower,99397248468847+c.upper)) = pointBounds19061 := by
 decide +kernel
def cuts19062 : List PrefixCut := [⟨43,224959574,224959711⟩,
⟨120,636850416,636850798⟩,
⟨128,679815894,679816301⟩]
theorem checked19062 : checkPrefixCuts (2^48) 2502426625 9 Manual.Count131072.C019062.packed 128 cuts19062 = true := by
 decide +kernel
def pointBounds19062 : List (Nat × Nat × Nat) := [(2502470656,99397777104483,99398157105011),(2502549504,99398188995325,99398568996098)]
theorem point_links_checked19062 : (cuts19062.take 2).map (fun c => (2502426625-1+2*2^9*c.k,99397552144909+c.lower,99397932145300+c.upper)) = pointBounds19062 := by
 decide +kernel
def cuts19063 : List PrefixCut := [⟨69,358114987,358115203⟩,
⟨128,675281456,675281860⟩]
theorem checked19063 : checkPrefixCuts (2^48) 2502557697 9 Manual.Count131072.C019063.packed 128 cuts19063 = true := by
 decide +kernel
def pointBounds19063 : List (Nat × Nat × Nat) := [(2502628352,99398590075790,99398970076804)]
theorem point_links_checked19063 : (cuts19063.take 1).map (fun c => (2502557697-1+2*2^9*c.k,99398231960803+c.lower,99398611961601+c.upper)) = pointBounds19063 := by
 decide +kernel
def cuts19064 : List PrefixCut := [⟨18,94811016,94811075⟩,
⟨95,495866222,495866521⟩,
⟨128,673671601,673672003⟩]
theorem checked19064 : checkPrefixCuts (2^48) 2502688769 9 Manual.Count131072.C019064.packed 128 cuts19064 = true := by
 decide +kernel
def pointBounds19064 : List (Nat × Nat × Nat) := [(2502707200,99399002053275,99399382054536),(2502786048,99399403108481,99399783109982)]
theorem point_links_checked19064 : (cuts19064.take 2).map (fun c => (2502688769-1+2*2^9*c.k,99398907242259+c.lower,99399287243461+c.upper)) = pointBounds19064 := by
 decide +kernel
def cuts19065 : List PrefixCut := [⟨44,235833023,235833164⟩,
⟨121,649683309,649683695⟩,
⟨128,687131615,687132024⟩]
theorem checked19065 : checkPrefixCuts (2^48) 2502819841 9 Manual.Count131072.C019065.packed 128 cuts19065 = true := by
 decide +kernel
def pointBounds19065 : List (Nat × Nat × Nat) := [(2502864896,99399816746883,99400196748628),(2502943744,99400230597169,99400610599159)]
theorem point_links_checked19065 : (cuts19065.take 2).map (fun c => (2502819841-1+2*2^9*c.k,99399580913860+c.lower,99399960915464+c.upper)) = pointBounds19065 := by
 decide +kernel
def cuts19066 : List PrefixCut := [⟨70,372565406,372565629⟩,
⟨128,683047177,683047584⟩]
theorem checked19066 : checkPrefixCuts (2^48) 2502950913 9 Manual.Count131072.C019066.packed 128 cuts19066 = true := by
 decide +kernel
def pointBounds19066 : List (Nat × Nat × Nat) := [(2503022592,99400640610881,99401020613117)]
theorem point_links_checked19066 : (cuts19066.take 1).map (fun c => (2502950913-1+2*2^9*c.k,99400268045475+c.lower,99400648047488+c.upper)) = pointBounds19066 := by
 decide +kernel
def cuts19067 : List PrefixCut := [⟨19,99856394,99856454⟩,
⟨96,504221833,504222133⟩,
⟨128,678625842,678626244⟩]
theorem checked19067 : checkPrefixCuts (2^48) 2503081985 9 Manual.Count131072.C019067.packed 128 cuts19067 = true := by
 decide +kernel
def pointBounds19067 : List (Nat × Nat × Nat) := [(2503101440,99401050949046,99401430951526),(2503180288,99401455314485,99401835317205)]
theorem point_links_checked19067 : (cuts19067.take 2).map (fun c => (2503081985-1+2*2^9*c.k,99400951092652+c.lower,99401331095072+c.upper)) = pointBounds19067 := by
 decide +kernel
def cuts19068 : List PrefixCut := [⟨45,233434595,233434738⟩,
⟨122,641934944,641935336⟩,
⟨128,674879772,674880185⟩]
theorem checked19068 : checkPrefixCuts (2^48) 2503213057 9 Manual.Count131072.C019068.packed 128 cuts19068 = true := by
 decide +kernel
def pointBounds19068 : List (Nat × Nat × Nat) := [(2503259136,99401863153089,99402243156054),(2503337984,99402271653438,99402651656652)]
theorem point_links_checked19068 : (cuts19068.take 2).map (fun c => (2503213057-1+2*2^9*c.k,99401629718494+c.lower,99402009721316+c.upper)) = pointBounds19068 := by
 decide +kernel
def cuts19069 : List PrefixCut := [⟨71,380152616,380152846⟩,
⟨128,683727039,683727448⟩]
theorem checked19069 : checkPrefixCuts (2^48) 2503344129 9 Manual.Count131072.C019069.packed 128 cuts19069 = true := by
 decide +kernel
def pointBounds19069 : List (Nat × Nat × Nat) := [(2503416832,99402684750882,99403064754347)]
theorem point_links_checked19069 : (cuts19069.take 1).map (fun c => (2503344129-1+2*2^9*c.k,99402304598266+c.lower,99402684601501+c.upper)) = pointBounds19069 := by
 decide +kernel
def cuts19070 : List PrefixCut := [⟨20,106586678,106586744⟩,
⟨97,509201980,509202288⟩,
⟨128,673235153,673235562⟩]
theorem checked19070 : checkPrefixCuts (2^48) 2503475201 9 Manual.Count131072.C019070.packed 128 cuts19070 = true := by
 decide +kernel
def pointBounds19070 : List (Nat × Nat × Nat) := [(2503495680,99403094911983,99403474915693),(2503574528,99403497527285,99403877531237)]
theorem point_links_checked19070 : (cuts19070.take 2).map (fun c => (2503475201-1+2*2^9*c.k,99402988325305+c.lower,99403368328949+c.upper)) = pointBounds19070 := by
 decide +kernel
def cuts19071 : List PrefixCut := [⟨46,239244070,239244213⟩,
⟨123,651839753,651840136⟩,
⟨128,679270723,679271122⟩]
theorem checked19071 : checkPrefixCuts (2^48) 2503606273 9 Manual.Count131072.C019071.packed 128 cuts19071 = true := by
 decide +kernel
def pointBounds19071 : List (Nat × Nat × Nat) := [(2503653376,99403900804528,99404280808724),(2503732224,99404313400211,99404693404647)]
theorem point_links_checked19071 : (cuts19071.take 2).map (fun c => (2503606273-1+2*2^9*c.k,99403661560458+c.lower,99404041564511+c.upper)) = pointBounds19071 := by
 decide +kernel
def cuts19072 : List PrefixCut := [⟨72,383690258,383690485⟩,
⟨128,693062662,693063065⟩]
theorem checked19072 : checkPrefixCuts (2^48) 2503737345 9 Manual.Count131072.C019072.packed 128 cuts19072 = true := by
 decide +kernel
def pointBounds19072 : List (Nat × Nat × Nat) := [(2503811072,99404724521439,99405104526118)]
theorem point_links_checked19072 : (cuts19072.take 1).map (fun c => (2503737345-1+2*2^9*c.k,99404340831181+c.lower,99404720835633+c.upper)) = pointBounds19072 := by
 decide +kernel
def cuts19073 : List PrefixCut := [⟨21,111178972,111179040⟩,
⟨98,517665385,517665695⟩,
⟨128,674366061,674366463⟩]
theorem checked19073 : checkPrefixCuts (2^48) 2503868417 9 Manual.Count131072.C019073.packed 128 cuts19073 = true := by
 decide +kernel
def pointBounds19073 : List (Nat × Nat × Nat) := [(2503889920,99405145072815,99405525077738),(2503968768,99405551559228,99405931564393)]
theorem point_links_checked19073 : (cuts19073.take 2).map (fun c => (2503868417-1+2*2^9*c.k,99405033893843+c.lower,99405413898698+c.upper)) = pointBounds19073 := by
 decide +kernel
def cuts19074 : List PrefixCut := [⟨47,255505750,255505902⟩,
⟨124,669048153,669048557⟩,
⟨128,690067764,690068180⟩]
theorem checked19074 : checkPrefixCuts (2^48) 2503999489 9 Manual.Count131072.C019074.packed 128 cuts19074 = true := by
 decide +kernel
def pointBounds19074 : List (Nat × Nat × Nat) := [(2504047616,99405963765654,99406343771063),(2504126464,99406377308057,99406757313718)]
theorem point_links_checked19074 : (cuts19074.take 2).map (fun c => (2503999489-1+2*2^9*c.k,99405708259904+c.lower,99406088265161+c.upper)) = pointBounds19074 := by
 decide +kernel
def cuts19075 : List PrefixCut := [⟨73,390936086,390936324⟩,
⟨128,683849505,683849921⟩]
theorem checked19075 : checkPrefixCuts (2^48) 2504130561 9 Manual.Count131072.C019075.packed 128 cuts19075 = true := by
 decide +kernel
def pointBounds19075 : List (Nat × Nat × Nat) := [(2504205312,99406789263754,99407169269665)]
theorem point_links_checked19075 : (cuts19075.take 1).map (fun c => (2504130561-1+2*2^9*c.k,99406398327668+c.lower,99406778333341+c.upper)) = pointBounds19075 := by
 decide +kernel
def cuts19076 : List PrefixCut := [⟨22,116106987,116107055⟩,
⟨99,532532566,532532884⟩,
⟨128,685274832,685275240⟩]
theorem checked19076 : checkPrefixCuts (2^48) 2504261633 9 Manual.Count131072.C019076.packed 128 cuts19076 = true := by
 decide +kernel
def pointBounds19076 : List (Nat × Nat × Nat) := [(2504284160,99407198284160,99407578290317),(2504363008,99407614709739,99407994716146)]
theorem point_links_checked19076 : (cuts19076.take 2).map (fun c => (2504261633-1+2*2^9*c.k,99407082177173+c.lower,99407462183262+c.upper)) = pointBounds19076 := by
 decide +kernel
def cuts19077 : List PrefixCut := [⟨48,261647098,261647255⟩,
⟨125,670404074,670404477⟩,
⟨128,688723099,688723513⟩]
theorem checked19077 : checkPrefixCuts (2^48) 2504392705 9 Manual.Count131072.C019077.packed 128 cuts19077 = true := by
 decide +kernel
def pointBounds19077 : List (Nat × Nat × Nat) := [(2504441856,99408029099103,99408409105757),(2504520704,99408437856079,99408817862979)]
theorem point_links_checked19077 : (cuts19077.take 2).map (fun c => (2504392705-1+2*2^9*c.k,99407767452005+c.lower,99408147458502+c.upper)) = pointBounds19077 := by
 decide +kernel
def cuts19078 : List PrefixCut := [⟨74,387390733,387390960⟩,
⟨128,675200946,675201347⟩]
theorem checked19078 : checkPrefixCuts (2^48) 2504523777 9 Manual.Count131072.C019078.packed 128 cuts19078 = true := by
 decide +kernel
def pointBounds19078 : List (Nat × Nat × Nat) := [(2504599552,99408843565837,99409223572975)]
theorem point_links_checked19078 : (cuts19078.take 1).map (fun c => (2504523777-1+2*2^9*c.k,99408456175104+c.lower,99408836182015+c.upper)) = pointBounds19078 := by
 decide +kernel
def cuts19079 : List PrefixCut := [⟨23,118336342,118336413⟩,
⟨100,526155701,526156014⟩,
⟨128,674716089,674716491⟩]
theorem checked19079 : checkPrefixCuts (2^48) 2504654849 9 Manual.Count131072.C019079.packed 128 cuts19079 = true := by
 decide +kernel
def pointBounds19079 : List (Nat × Nat × Nat) := [(2504678400,99409249712392,99409629719775),(2504757248,99409657531751,99410037539376)]
theorem point_links_checked19079 : (cuts19079.take 2).map (fun c => (2504654849-1+2*2^9*c.k,99409131376050+c.lower,99409511383362+c.upper)) = pointBounds19079 := by
 decide +kernel
def cuts19080 : List PrefixCut := [⟨49,266775148,266775300⟩,
⟨126,679513187,679513582⟩,
⟨128,689514028,689514428⟩]
theorem checked19080 : checkPrefixCuts (2^48) 2504785921 9 Manual.Count131072.C019080.packed 128 cuts19080 = true := by
 decide +kernel
def pointBounds19080 : List (Nat × Nat × Nat) := [(2504836096,99410072867287,99410452875153),(2504914944,99410485605326,99410865613435)]
theorem point_links_checked19080 : (cuts19080.take 2).map (fun c => (2504785921-1+2*2^9*c.k,99409806092139+c.lower,99410186099853+c.upper)) = pointBounds19080 := by
 decide +kernel
def cuts19081 : List PrefixCut := [⟨75,400364490,400364725⟩,
⟨128,683073051,683073454⟩]
theorem checked19081 : checkPrefixCuts (2^48) 2504916993 9 Manual.Count131072.C019081.packed 128 cuts19081 = true := by
 decide +kernel
def pointBounds19081 : List (Nat × Nat × Nat) := [(2504993792,99410895970657,99411275979006)]
theorem point_links_checked19081 : (cuts19081.take 1).map (fun c => (2504916993-1+2*2^9*c.k,99410495606167+c.lower,99410875614281+c.upper)) = pointBounds19081 := by
 decide +kernel
def cuts19082 : List PrefixCut := [⟨24,123935868,123935941⟩,
⟨101,527421388,527421705⟩,
⟨128,667868658,667869060⟩]
theorem checked19082 : checkPrefixCuts (2^48) 2505048065 9 Manual.Count131072.C019082.packed 128 cuts19082 = true := by
 decide +kernel
def pointBounds19082 : List (Nat × Nat × Nat) := [(2505072640,99411302615086,99411682623676),(2505151488,99411706100606,99412086109440)]
theorem point_links_checked19082 : (cuts19082.take 2).map (fun c => (2505048065-1+2*2^9*c.k,99411178679218+c.lower,99411558687735+c.upper)) = pointBounds19082 := by
 decide +kernel
def cuts19083 : List PrefixCut := [⟨50,268868037,268868194⟩,
⟨127,676822213,676822618⟩,
⟨128,682889185,682889594⟩]
theorem checked19083 : checkPrefixCuts (2^48) 2505179137 9 Manual.Count131072.C019083.packed 128 cuts19083 = true := by
 decide +kernel
def pointBounds19083 : List (Nat × Nat × Nat) := [(2505230336,99412115415913,99412495424989),(2505309184,99412523370089,99412903379413)]
theorem point_links_checked19083 : (cuts19083.take 2).map (fun c => (2505179137-1+2*2^9*c.k,99411846547876+c.lower,99412226556795+c.upper)) = pointBounds19083 := by
 decide +kernel
def cuts19084 : List PrefixCut := [⟨76,402323841,402324088⟩,
⟨128,691616395,691616813⟩]
theorem checked19084 : checkPrefixCuts (2^48) 2505310209 9 Manual.Count131072.C019084.packed 128 cuts19084 = true := by
 decide +kernel
def pointBounds19084 : List (Nat × Nat × Nat) := [(2505388032,99412931760902,99413311770477)]
theorem point_links_checked19084 : (cuts19084.take 1).map (fun c => (2505310209-1+2*2^9*c.k,99412529437061+c.lower,99412909446389+c.upper)) = pointBounds19084 := by
 decide +kernel
def cuts19085 : List PrefixCut := [⟨25,133465692,133465769⟩,
⟨102,538460489,538460809⟩,
⟨128,676638876,676639281⟩]
theorem checked19085 : checkPrefixCuts (2^48) 2505441281 9 Manual.Count131072.C019085.packed 128 cuts19085 = true := by
 decide +kernel
def pointBounds19085 : List (Nat × Nat × Nat) := [(2505466880,99413354519148,99413734528971),(2505545728,99413759513945,99414139524011)]
theorem point_links_checked19085 : (cuts19085.take 2).map (fun c => (2505441281-1+2*2^9*c.k,99413221053456+c.lower,99413601063202+c.upper)) = pointBounds19085 := by
 decide +kernel
def cuts19086 : List PrefixCut := [⟨51,269949145,269949306⟩,
⟨128,680760031,680760438⟩]
theorem checked19086 : checkPrefixCuts (2^48) 2505572353 9 Manual.Count131072.C019086.packed 128 cuts19086 = true := by
 decide +kernel
def pointBounds19086 : List (Nat × Nat × Nat) := [(2505624576,99414167641477,99414547651789),(2505703424,99414578452363,99414958462921)]
theorem point_links_checked19086 : (cuts19086.take 2).map (fun c => (2505572353-1+2*2^9*c.k,99413897692332+c.lower,99414277702483+c.upper)) = pointBounds19086 := by
 decide +kernel
def cuts19087 : List PrefixCut := [⟨77,416863823,416864066⟩,
⟨128,690384911,690385311⟩]
theorem checked19087 : checkPrefixCuts (2^48) 2505703425 9 Manual.Count131072.C019087.packed 128 cuts19087 = true := by
 decide +kernel
def pointBounds19087 : List (Nat × Nat × Nat) := [(2505782272,99414995316186,99415375326987)]
theorem point_links_checked19087 : (cuts19087.take 1).map (fun c => (2505703425-1+2*2^9*c.k,99414578452363+c.lower,99414958462921+c.upper)) = pointBounds19087 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000283
