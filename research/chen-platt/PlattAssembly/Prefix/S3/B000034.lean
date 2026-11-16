import PlattAssemblyKernel
import PlattCertificates.Count131072.C021088
import PlattCertificates.Count131072.C021089
import PlattCertificates.Count131072.C021090
import PlattCertificates.Count131072.C021091
import PlattCertificates.Count131072.C021092
import PlattCertificates.Count131072.C021093
import PlattCertificates.Count131072.C021094
import PlattCertificates.Count131072.C021095
import PlattCertificates.Count131072.C021096
import PlattCertificates.Count131072.C021097
import PlattCertificates.Count131072.C021098
import PlattCertificates.Count131072.C021099
import PlattCertificates.Count131072.C021100
import PlattCertificates.Count131072.C021101
import PlattCertificates.Count131072.C021102
import PlattCertificates.Count131072.C021103
import PlattCertificates.Count131072.C021104
import PlattCertificates.Count131072.C021105
import PlattCertificates.Count131072.C021106
import PlattCertificates.Count131072.C021107
import PlattCertificates.Count131072.C021108
import PlattCertificates.Count131072.C021109
import PlattCertificates.Count131072.C021110
import PlattCertificates.Count131072.C021111
import PlattCertificates.Count131072.C021112
import PlattCertificates.Count131072.C021113
import PlattCertificates.Count131072.C021114
import PlattCertificates.Count131072.C021115
import PlattCertificates.Count131072.C021116
import PlattCertificates.Count131072.C021117
import PlattCertificates.Count131072.C021118
import PlattCertificates.Count131072.C021119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21088 : List PrefixCut := [⟨2,9762207,9762213⟩,
⟨87,430038804,430039051⟩,
⟨128,627512345,627512706⟩]
theorem checked21088 : checkPrefixCuts (2^48) 2767978497 9 Manual.Count131072.C021088.packed 128 cuts21088 = true := by
 decide +kernel
def pointBounds21088 : List (Nat × Nat × Nat) := [(2767980544,100706361280492,100706742049947),(2768067584,100706781557089,100707162326785)]
theorem point_links_checked21088 : (cuts21088.take 2).map (fun c => (2767978497-1+2*2^9*c.k,100706351518285+c.lower,100706732287734+c.upper)) = pointBounds21088 := by
 decide +kernel
def cuts21089 : List PrefixCut := [⟨44,211807900,211808023⟩,
⟨128,612128508,612128866⟩]
theorem checked21089 : checkPrefixCuts (2^48) 2768109569 9 Manual.Count131072.C021089.packed 128 cuts21089 = true := by
 decide +kernel
def pointBounds21089 : List (Nat × Nat × Nat) := [(2768154624,100707190838530,100707571608463)]
theorem point_links_checked21089 : (cuts21089.take 1).map (fun c => (2768109569-1+2*2^9*c.k,100706979030630+c.lower,100707359800440+c.upper)) = pointBounds21089 := by
 decide +kernel
def cuts21090 : List PrefixCut := [⟨1,4473922,4473925⟩,
⟨86,414543081,414543323⟩,
⟨128,617996833,617997190⟩]
theorem checked21090 : checkPrefixCuts (2^48) 2768240641 9 Manual.Count131072.C021090.packed 128 cuts21090 = true := by
 decide +kernel
def pointBounds21090 : List (Nat × Nat × Nat) := [(2768241664,100707595633060,100707976403231),(2768328704,100708005702219,100708386472629)]
theorem point_links_checked21090 : (cuts21090.take 2).map (fun c => (2768240641-1+2*2^9*c.k,100707591159138+c.lower,100707971929306+c.upper)) = pointBounds21090 := by
 decide +kernel
def cuts21091 : List PrefixCut := [⟨43,208025921,208026040⟩,
⟨128,611663904,611664257⟩]
theorem checked21091 : checkPrefixCuts (2^48) 2768371713 9 Manual.Count131072.C021091.packed 128 cuts21091 = true := by
 decide +kernel
def pointBounds21091 : List (Nat × Nat × Nat) := [(2768415744,100708417181892,100708797952536),(2768502784,100708820819875,100709201590753)]
theorem point_links_checked21091 : (cuts21091.take 2).map (fun c => (2768371713-1+2*2^9*c.k,100708209155971+c.lower,100708589926496+c.upper)) = pointBounds21091 := by
 decide +kernel
def cuts21092 : List PrefixCut := [⟨85,403625300,403625533⟩,
⟨128,610923179,610923532⟩]
theorem checked21092 : checkPrefixCuts (2^48) 2768502785 9 Manual.Count131072.C021092.packed 128 cuts21092 = true := by
 decide +kernel
def pointBounds21092 : List (Nat × Nat × Nat) := [(2768589824,100709224445175,100709605216286)]
theorem point_links_checked21092 : (cuts21092.take 1).map (fun c => (2768502785-1+2*2^9*c.k,100708820819875+c.lower,100709201590753+c.upper)) = pointBounds21092 := by
 decide +kernel
def cuts21093 : List PrefixCut := [⟨42,202313017,202313132⟩,
⟨127,610894330,610894683⟩,
⟨128,615774050,615774406⟩]
theorem checked21093 : checkPrefixCuts (2^48) 2768633857 9 Manual.Count131072.C021093.packed 128 cuts21093 = true := by
 decide +kernel
def pointBounds21093 : List (Nat × Nat × Nat) := [(2768676864,100709634056071,100710014827417),(2768763904,100710042637384,100710423408968)]
theorem point_links_checked21093 : (cuts21093.take 2).map (fun c => (2768633857-1+2*2^9*c.k,100709431743054+c.lower,100709812514285+c.upper)) = pointBounds21093 := by
 decide +kernel
def cuts21094 : List PrefixCut := [⟨84,397487639,397487870⟩,
⟨128,612186870,612187225⟩]
theorem checked21094 : checkPrefixCuts (2^48) 2768764929 9 Manual.Count131072.C021094.packed 128 cuts21094 = true := by
 decide +kernel
def pointBounds21094 : List (Nat × Nat × Nat) := [(2768850944,100710445004743,100710825776561)]
theorem point_links_checked21094 : (cuts21094.take 1).map (fun c => (2768764929-1+2*2^9*c.k,100710047517104+c.lower,100710428288691+c.upper)) = pointBounds21094 := by
 decide +kernel
def cuts21095 : List PrefixCut := [⟨41,196296259,196296374⟩,
⟨126,603720924,603721274⟩,
⟨128,613072837,613073193⟩]
theorem checked21095 : checkPrefixCuts (2^48) 2768896001 9 Manual.Count131072.C021095.packed 128 cuts21095 = true := by
 decide +kernel
def pointBounds21095 : List (Nat × Nat × Nat) := [(2768937984,100710856000233,100711236772290),(2769025024,100711263424898,100711644197190)]
theorem point_links_checked21095 : (cuts21095.take 2).map (fun c => (2768896001-1+2*2^9*c.k,100710659703974+c.lower,100711040475916+c.upper)) = pointBounds21095 := by
 decide +kernel
def cuts21096 : List PrefixCut := [⟨83,401414418,401414651⟩,
⟨128,619549352,619549707⟩]
theorem checked21096 : checkPrefixCuts (2^48) 2769027073 9 Manual.Count131072.C021096.packed 128 cuts21096 = true := by
 decide +kernel
def pointBounds21096 : List (Nat × Nat × Nat) := [(2769112064,100711674191229,100712054963760)]
theorem point_links_checked21096 : (cuts21096.take 1).map (fun c => (2769027073-1+2*2^9*c.k,100711272776811+c.lower,100711653549109+c.upper)) = pointBounds21096 := by
 decide +kernel
def cuts21097 : List PrefixCut := [⟨40,183775297,183775401⟩,
⟨125,582826776,582827112⟩,
⟨128,597666453,597666798⟩]
theorem checked21097 : checkPrefixCuts (2^48) 2769158145 9 Manual.Count131072.C021097.packed 128 cuts21097 = true := by
 decide +kernel
def pointBounds21097 : List (Nat × Nat × Nat) := [(2769199104,100712076101460,100712456874217),(2769286144,100712475152939,100712855925928)]
theorem point_links_checked21097 : (cuts21097.take 2).map (fun c => (2769158145-1+2*2^9*c.k,100711892326163+c.lower,100712273098816+c.upper)) = pointBounds21097 := by
 decide +kernel
def cuts21098 : List PrefixCut := [⟨82,390805920,390806146⟩,
⟨128,612985773,612986127⟩]
theorem checked21098 : checkPrefixCuts (2^48) 2769289217 9 Manual.Count131072.C021098.packed 128 cuts21098 = true := by
 decide +kernel
def pointBounds21098 : List (Nat × Nat × Nat) := [(2769373184,100712880798536,100713261571760)]
theorem point_links_checked21098 : (cuts21098.take 1).map (fun c => (2769289217-1+2*2^9*c.k,100712489992616+c.lower,100712870765614+c.upper)) = pointBounds21098 := by
 decide +kernel
def cuts21099 : List PrefixCut := [⟨39,185993914,185994027⟩,
⟨124,598626671,598627019⟩,
⟨128,618038386,618038746⟩]
theorem checked21099 : checkPrefixCuts (2^48) 2769420289 9 Manual.Count131072.C021099.packed 128 cuts21099 = true := by
 decide +kernel
def pointBounds21099 : List (Nat × Nat × Nat) := [(2769460224,100713288972303,100713669745768),(2769547264,100713701605060,100714082378760)]
theorem point_links_checked21099 : (cuts21099.take 2).map (fun c => (2769420289-1+2*2^9*c.k,100713102978389+c.lower,100713483751741+c.upper)) = pointBounds21099 := by
 decide +kernel
def cuts21100 : List PrefixCut := [⟨81,386907008,386907229⟩,
⟨128,616687955,616688306⟩]
theorem checked21100 : checkPrefixCuts (2^48) 2769551361 9 Manual.Count131072.C021100.packed 128 cuts21100 = true := by
 decide +kernel
def pointBounds21100 : List (Nat × Nat × Nat) := [(2769634304,100714107923783,100714488697716)]
theorem point_links_checked21100 : (cuts21100.take 1).map (fun c => (2769551361-1+2*2^9*c.k,100713721016775+c.lower,100714101790487+c.upper)) = pointBounds21100 := by
 decide +kernel
def cuts21101 : List PrefixCut := [⟨38,179269005,179269109⟩,
⟨123,589322294,589322639⟩,
⟨128,614524655,614525014⟩]
theorem checked21101 : checkPrefixCuts (2^48) 2769682433 9 Manual.Count131072.C021101.packed 128 cuts21101 = true := by
 decide +kernel
def pointBounds21101 : List (Nat × Nat × Nat) := [(2769721344,100714516973735,100714897747902),(2769808384,100714927027024,100715307801432)]
theorem point_links_checked21101 : (cuts21101.take 2).map (fun c => (2769682433-1+2*2^9*c.k,100714337704730+c.lower,100714718478793+c.upper)) = pointBounds21101 := by
 decide +kernel
def cuts21102 : List PrefixCut := [⟨80,385447808,385448035⟩,
⟨128,609719672,609720032⟩]
theorem checked21102 : checkPrefixCuts (2^48) 2769813505 9 Manual.Count131072.C021102.packed 128 cuts21102 = true := by
 decide +kernel
def pointBounds21102 : List (Nat × Nat × Nat) := [(2769895424,100715337677193,100715718451842)]
theorem point_links_checked21102 : (cuts21102.take 1).map (fun c => (2769813505-1+2*2^9*c.k,100714952229385+c.lower,100715333003807+c.upper)) = pointBounds21102 := by
 decide +kernel
def cuts21103 : List PrefixCut := [⟨37,177829426,177829528⟩,
⟨122,581035913,581036251⟩,
⟨128,612231050,612231406⟩]
theorem checked21103 : checkPrefixCuts (2^48) 2769944577 9 Manual.Count131072.C021103.packed 128 cuts21103 = true := by
 decide +kernel
def pointBounds21103 : List (Nat × Nat × Nat) := [(2769982464,100715739778483,100716120553367),(2770069504,100716142984970,100716523760090)]
theorem point_links_checked21103 : (cuts21103.take 2).map (fun c => (2769944577-1+2*2^9*c.k,100715561949057+c.lower,100715942723839+c.upper)) = pointBounds21103 := by
 decide +kernel
def cuts21104 : List PrefixCut := [⟨79,374437358,374437577⟩,
⟨128,605089348,605089701⟩]
theorem checked21104 : checkPrefixCuts (2^48) 2770075649 9 Manual.Count131072.C021104.packed 128 cuts21104 = true := by
 decide +kernel
def pointBounds21104 : List (Nat × Nat × Nat) := [(2770156544,100716548617465,100716929392822)]
theorem point_links_checked21104 : (cuts21104.take 1).map (fun c => (2770075649-1+2*2^9*c.k,100716174180107+c.lower,100716554955245+c.upper)) = pointBounds21104 := by
 decide +kernel
def cuts21105 : List PrefixCut := [⟨36,172122635,172122738⟩,
⟨121,572242984,572243320⟩,
⟨128,605162430,605162786⟩]
theorem checked21105 : checkPrefixCuts (2^48) 2770206721 9 Manual.Count131072.C021105.packed 128 cuts21105 = true := by
 decide +kernel
def pointBounds21105 : List (Nat × Nat × Nat) := [(2770243584,100716951392090,100717332167684),(2770330624,100717351512439,100717732288266)]
theorem point_links_checked21105 : (cuts21105.take 2).map (fun c => (2770206721-1+2*2^9*c.k,100716779269455+c.lower,100717160044946+c.upper)) = pointBounds21105 := by
 decide +kernel
def cuts21106 : List PrefixCut := [⟨78,375316491,375316706⟩,
⟨128,616208271,616208624⟩]
theorem checked21106 : checkPrefixCuts (2^48) 2770337793 9 Manual.Count131072.C021106.packed 128 cuts21106 = true := by
 decide +kernel
def pointBounds21106 : List (Nat × Nat × Nat) := [(2770417664,100717759748376,100718140524438)]
theorem point_links_checked21106 : (cuts21106.take 1).map (fun c => (2770337793-1+2*2^9*c.k,100717384431885+c.lower,100717765207732+c.upper)) = pointBounds21106 := by
 decide +kernel
def cuts21107 : List PrefixCut := [⟨35,171293603,171293704⟩,
⟨120,577979879,577980217⟩,
⟨128,614858366,614858726⟩]
theorem checked21107 : checkPrefixCuts (2^48) 2770468865 9 Manual.Count131072.C021107.packed 128 cuts21107 = true := by
 decide +kernel
def pointBounds21107 : List (Nat × Nat × Nat) := [(2770504704,100718171933759,100718552710060),(2770591744,100718578620035,100718959396573)]
theorem point_links_checked21107 : (cuts21107.take 2).map (fun c => (2770468865-1+2*2^9*c.k,100718000640156+c.lower,100718381416356+c.upper)) = pointBounds21107 := by
 decide +kernel
def cuts21108 : List PrefixCut := [⟨77,371522129,371522344⟩,
⟨128,616861089,616861445⟩]
theorem checked21108 : checkPrefixCuts (2^48) 2770599937 9 Manual.Count131072.C021108.packed 128 cuts21108 = true := by
 decide +kernel
def pointBounds21108 : List (Nat × Nat × Nat) := [(2770678784,100718987020651,100719367797426)]
theorem point_links_checked21108 : (cuts21108.take 1).map (fun c => (2770599937-1+2*2^9*c.k,100718615498522+c.lower,100718996275082+c.upper)) = pointBounds21108 := by
 decide +kernel
def cuts21109 : List PrefixCut := [⟨34,162642450,162642545⟩,
⟨119,567563416,567563748⟩,
⟨128,612463560,612463917⟩]
theorem checked21109 : checkPrefixCuts (2^48) 2770731009 9 Manual.Count131072.C021109.packed 128 cuts21109 = true := by
 decide +kernel
def pointBounds21109 : List (Nat × Nat × Nat) := [(2770765824,100719395002061,100719775779072),(2770852864,100719799923027,100720180700275)]
theorem point_links_checked21109 : (cuts21109.take 2).map (fun c => (2770731009-1+2*2^9*c.k,100719232359611+c.lower,100719613136527+c.upper)) = pointBounds21109 := by
 decide +kernel
def cuts21110 : List PrefixCut := [⟨76,369658512,369658726⟩,
⟨128,613958495,613958855⟩]
theorem checked21110 : checkPrefixCuts (2^48) 2770862081 9 Manual.Count131072.C021110.packed 128 cuts21110 = true := by
 decide +kernel
def pointBounds21110 : List (Nat × Nat × Nat) := [(2770939904,100720214481683,100720595259170)]
theorem point_links_checked21110 : (cuts21110.take 1).map (fun c => (2770862081-1+2*2^9*c.k,100719844823171+c.lower,100720225600444+c.upper)) = pointBounds21110 := by
 decide +kernel
def cuts21111 : List PrefixCut := [⟨33,159275003,159275095⟩,
⟨118,574315540,574315871⟩,
⟨128,621141360,621141718⟩]
theorem checked21111 : checkPrefixCuts (2^48) 2770993153 9 Manual.Count131072.C021111.packed 128 cuts21111 = true := by
 decide +kernel
def pointBounds21111 : List (Nat × Nat × Nat) := [(2771026944,100720618056669,100720998834394),(2771113984,100721033097206,100721413875170)]
theorem point_links_checked21111 : (cuts21111.take 2).map (fun c => (2770993153-1+2*2^9*c.k,100720458781666+c.lower,100720839559299+c.upper)) = pointBounds21111 := by
 decide +kernel
def cuts21112 : List PrefixCut := [⟨75,363529236,363529446⟩,
⟨128,618978867,618979223⟩]
theorem checked21112 : checkPrefixCuts (2^48) 2771124225 9 Manual.Count131072.C021112.packed 128 cuts21112 = true := by
 decide +kernel
def pointBounds21112 : List (Nat × Nat × Nat) := [(2771201024,100721443452262,100721824230463)]
theorem point_links_checked21112 : (cuts21112.take 1).map (fun c => (2771124225-1+2*2^9*c.k,100721079923026+c.lower,100721460701017+c.upper)) = pointBounds21112 := by
 decide +kernel
def cuts21113 : List PrefixCut := [⟨32,156517606,156517694⟩,
⟨117,563495260,563495580⟩,
⟨128,616004296,616004645⟩]
theorem checked21113 : checkPrefixCuts (2^48) 2771255297 9 Manual.Count131072.C021113.packed 128 cuts21113 = true := by
 decide +kernel
def pointBounds21113 : List (Nat × Nat × Nat) := [(2771288064,100721855419499,100722236197934),(2771375104,100722262397153,100722643175820)]
theorem point_links_checked21113 : (cuts21113.take 2).map (fun c => (2771255297-1+2*2^9*c.k,100721698901893+c.lower,100722079680240+c.upper)) = pointBounds21113 := by
 decide +kernel
def cuts21114 : List PrefixCut := [⟨74,356588609,356588819⟩,
⟨128,611607910,611608268⟩]
theorem checked21114 : checkPrefixCuts (2^48) 2771386369 9 Manual.Count131072.C021114.packed 128 cuts21114 = true := by
 decide +kernel
def pointBounds21114 : List (Nat × Nat × Nat) := [(2771462144,100722671494798,100723052273704)]
theorem point_links_checked21114 : (cuts21114.take 1).map (fun c => (2771386369-1+2*2^9*c.k,100722314906189+c.lower,100722695684885+c.upper)) = pointBounds21114 := by
 decide +kernel
def cuts21115 : List PrefixCut := [⟨31,148581217,148581304⟩,
⟨116,560090509,560090834⟩,
⟨128,619195681,619196040⟩]
theorem checked21115 : checkPrefixCuts (2^48) 2771517441 9 Manual.Count131072.C021115.packed 128 cuts21115 = true := by
 decide +kernel
def pointBounds21115 : List (Nat × Nat × Nat) := [(2771549184,100723075095316,100723455874457),(2771636224,100723486604608,100723867383987)]
theorem point_links_checked21115 : (cuts21115.take 2).map (fun c => (2771517441-1+2*2^9*c.k,100722926514099+c.lower,100723307293153+c.upper)) = pointBounds21115 := by
 decide +kernel
def cuts21116 : List PrefixCut := [⟨73,347618222,347618428⟩,
⟨128,613987216,613987571⟩]
theorem checked21116 : checkPrefixCuts (2^48) 2771648513 9 Manual.Count131072.C021116.packed 128 cuts21116 = true := by
 decide +kernel
def pointBounds21116 : List (Nat × Nat × Nat) := [(2771723264,100723893328002,100724274107621)]
theorem point_links_checked21116 : (cuts21116.take 1).map (fun c => (2771648513-1+2*2^9*c.k,100723545709780+c.lower,100723926489193+c.upper)) = pointBounds21116 := by
 decide +kernel
def cuts21117 : List PrefixCut := [⟨30,144708296,144708381⟩,
⟨115,546735012,546735330⟩,
⟨128,610607247,610607602⟩]
theorem checked21117 : checkPrefixCuts (2^48) 2771779585 9 Manual.Count131072.C021117.packed 128 cuts21117 = true := by
 decide +kernel
def pointBounds21117 : List (Nat × Nat × Nat) := [(2771810304,100724304405292,100724685185145),(2771897344,100724706432008,100725087212094)]
theorem point_links_checked21117 : (cuts21117.take 2).map (fun c => (2771779585-1+2*2^9*c.k,100724159696996+c.lower,100724540476764+c.upper)) = pointBounds21117 := by
 decide +kernel
def cuts21118 : List PrefixCut := [⟨72,342711260,342711460⟩,
⟨128,616163055,616163419⟩]
theorem checked21118 : checkPrefixCuts (2^48) 2771910657 9 Manual.Count131072.C021118.packed 128 cuts21118 = true := by
 decide +kernel
def pointBounds21118 : List (Nat × Nat × Nat) := [(2771984384,100725113015503,100725493795826)]
theorem point_links_checked21118 : (cuts21118.take 1).map (fun c => (2771910657-1+2*2^9*c.k,100724770304243+c.lower,100725151084366+c.upper)) = pointBounds21118 := by
 decide +kernel
def cuts21119 : List PrefixCut := [⟨29,135556018,135556101⟩,
⟨114,539270997,539271308⟩,
⟨128,607604794,607605146⟩]
theorem checked21119 : checkPrefixCuts (2^48) 2772041729 9 Manual.Count131072.C021119.packed 128 cuts21119 = true := by
 decide +kernel
def pointBounds21119 : List (Nat × Nat × Nat) := [(2772071424,100725522023316,100725902803886),(2772158464,100725925738295,100726306519093)]
theorem point_links_checked21119 : (cuts21119.take 2).map (fun c => (2772041729-1+2*2^9*c.k,100725386467298+c.lower,100725767247785+c.upper)) = pointBounds21119 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000034
