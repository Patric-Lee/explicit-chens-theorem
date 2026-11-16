import PlattAssemblyKernel
import PlattCertificates.Count131072.C020096
import PlattCertificates.Count131072.C020097
import PlattCertificates.Count131072.C020098
import PlattCertificates.Count131072.C020099
import PlattCertificates.Count131072.C020100
import PlattCertificates.Count131072.C020101
import PlattCertificates.Count131072.C020102
import PlattCertificates.Count131072.C020103
import PlattCertificates.Count131072.C020104
import PlattCertificates.Count131072.C020105
import PlattCertificates.Count131072.C020106
import PlattCertificates.Count131072.C020107
import PlattCertificates.Count131072.C020108
import PlattCertificates.Count131072.C020109
import PlattCertificates.Count131072.C020110
import PlattCertificates.Count131072.C020111
import PlattCertificates.Count131072.C020112
import PlattCertificates.Count131072.C020113
import PlattCertificates.Count131072.C020114
import PlattCertificates.Count131072.C020115
import PlattCertificates.Count131072.C020116
import PlattCertificates.Count131072.C020117
import PlattCertificates.Count131072.C020118
import PlattCertificates.Count131072.C020119
import PlattCertificates.Count131072.C020120
import PlattCertificates.Count131072.C020121
import PlattCertificates.Count131072.C020122
import PlattCertificates.Count131072.C020123
import PlattCertificates.Count131072.C020124
import PlattCertificates.Count131072.C020125
import PlattCertificates.Count131072.C020126
import PlattCertificates.Count131072.C020127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20096 : List PrefixCut := [⟨36,184486333,184486440⟩,
⟨117,587594329,587594674⟩,
⟨128,644677146,644677523⟩]
theorem checked20096 : checkPrefixCuts (2^48) 2637955073 9 Manual.Count131072.C020096.packed 128 cuts20096 = true := by
 decide +kernel
def pointBounds20096 : List (Nat × Nat × Nat) := [(2637991936,100083063927578,100083444333824),(2638074880,100083467035574,100083847442058)]
theorem point_links_checked20096 : (cuts20096.take 2).map (fun c => (2637955073-1+2*2^9*c.k,100082879441245+c.lower,100083259847384+c.upper)) = pointBounds20096 := by
 decide +kernel
def cuts20097 : List PrefixCut := [⟨70,361269910,361270120⟩,
⟨128,654994430,654994809⟩]
theorem checked20097 : checkPrefixCuts (2^48) 2638086145 9 Manual.Count131072.C020097.packed 128 cuts20097 = true := by
 decide +kernel
def pointBounds20097 : List (Nat × Nat × Nat) := [(2638157824,100083885388301,100084265795027)]
theorem point_links_checked20097 : (cuts20097.take 1).map (fun c => (2638086145-1+2*2^9*c.k,100083524118391+c.lower,100083904524907+c.upper)) = pointBounds20097 := by
 decide +kernel
def cuts20098 : List PrefixCut := [⟨23,118533544,118533616⟩,
⟨104,531098821,531099137⟩,
⟨128,651761290,651761678⟩]
theorem checked20098 : checkPrefixCuts (2^48) 2638217217 9 Manual.Count131072.C020098.packed 128 cuts20098 = true := by
 decide +kernel
def pointBounds20098 : List (Nat × Nat × Nat) := [(2638240768,100084297646365,100084678053332),(2638323712,100084710211642,100085090618853)]
theorem point_links_checked20098 : (cuts20098.take 2).map (fun c => (2638217217-1+2*2^9*c.k,100084179112821+c.lower,100084559519716+c.upper)) = pointBounds20098 := by
 decide +kernel
def cuts20099 : List PrefixCut := [⟨57,286342120,286342289⟩,
⟨128,644367559,644367932⟩]
theorem checked20099 : checkPrefixCuts (2^48) 2638348289 9 Manual.Count131072.C020099.packed 128 cuts20099 = true := by
 decide +kernel
def pointBounds20099 : List (Nat × Nat × Nat) := [(2638406656,100085117216231,100085497623683)]
theorem point_links_checked20099 : (cuts20099.take 1).map (fun c => (2638348289-1+2*2^9*c.k,100084830874111+c.lower,100085211281394+c.upper)) = pointBounds20099 := by
 decide +kernel
def cuts20100 : List PrefixCut := [⟨10,51846732,51846763⟩,
⟨91,467040006,467040279⟩,
⟨128,657457026,657457411⟩]
theorem checked20100 : checkPrefixCuts (2^48) 2638479361 9 Manual.Count131072.C020100.packed 128 cuts20100 = true := by
 decide +kernel
def pointBounds20100 : List (Nat × Nat × Nat) := [(2638489600,100085527088402,100085907496089),(2638572544,100085942281676,100086322689605)]
theorem point_links_checked20100 : (cuts20100.take 2).map (fun c => (2638479361-1+2*2^9*c.k,100085475241670+c.lower,100085855649326+c.upper)) = pointBounds20100 := by
 decide +kernel
def cuts20101 : List PrefixCut := [⟨44,219002776,219002904⟩,
⟨125,617742412,617742776⟩,
⟨128,631502867,631503239⟩]
theorem checked20101 : checkPrefixCuts (2^48) 2638610433 9 Manual.Count131072.C020101.packed 128 cuts20101 = true := by
 decide +kernel
def pointBounds20101 : List (Nat × Nat × Nat) := [(2638655488,100086351701472,100086732109641),(2638738432,100086750441108,100087130849513)]
theorem point_links_checked20101 : (cuts20101.take 2).map (fun c => (2638610433-1+2*2^9*c.k,100086132698696+c.lower,100086513106737+c.upper)) = pointBounds20101 := by
 decide +kernel
def cuts20102 : List PrefixCut := [⟨78,387313427,387313653⟩,
⟨128,634778247,634778619⟩]
theorem checked20102 : checkPrefixCuts (2^48) 2638741505 9 Manual.Count131072.C020102.packed 128 cuts20102 = true := by
 decide +kernel
def pointBounds20102 : List (Nat × Nat × Nat) := [(2638821376,100087151514990,100087531923629)]
theorem point_links_checked20102 : (cuts20102.take 1).map (fun c => (2638741505-1+2*2^9*c.k,100086764201563+c.lower,100087144609976+c.upper)) = pointBounds20102 := by
 decide +kernel
def cuts20103 : List PrefixCut := [⟨31,159996296,159996386⟩,
⟨112,561471620,561471948⟩,
⟨128,642106475,642106851⟩]
theorem checked20103 : checkPrefixCuts (2^48) 2638872577 9 Manual.Count131072.C020103.packed 128 cuts20103 = true := by
 decide +kernel
def pointBounds20103 : List (Nat × Nat × Nat) := [(2638904320,100087558976106,100087939384981),(2638987264,100087960451430,100088340860543)]
theorem point_links_checked20103 : (cuts20103.take 2).map (fun c => (2638872577-1+2*2^9*c.k,100087398979810+c.lower,100087779388595+c.upper)) = pointBounds20103 := by
 decide +kernel
def cuts20104 : List PrefixCut := [⟨65,322640963,322641152⟩,
⟨128,639727898,639728274⟩]
theorem checked20104 : checkPrefixCuts (2^48) 2639003649 9 Manual.Count131072.C020104.packed 128 cuts20104 = true := by
 decide +kernel
def pointBounds20104 : List (Nat × Nat × Nat) := [(2639070208,100088363727248,100088744136598)]
theorem point_links_checked20104 : (cuts20104.take 1).map (fun c => (2639003649-1+2*2^9*c.k,100088041086285+c.lower,100088421495446+c.upper)) = pointBounds20104 := by
 decide +kernel
def cuts20105 : List PrefixCut := [⟨18,90975748,90975800⟩,
⟨99,494759573,494759864⟩,
⟨128,638523151,638523527⟩]
theorem checked20105 : checkPrefixCuts (2^48) 2639134721 9 Manual.Count131072.C020105.packed 128 cuts20105 = true := by
 decide +kernel
def pointBounds20105 : List (Nat × Nat × Nat) := [(2639153152,100088771789931,100089152199520),(2639236096,100089175573756,100089555983584)]
theorem point_links_checked20105 : (cuts20105.take 2).map (fun c => (2639134721-1+2*2^9*c.k,100088680814183+c.lower,100089061223720+c.upper)) = pointBounds20105 := by
 decide +kernel
def cuts20106 : List PrefixCut := [⟨52,256808029,256808177⟩,
⟨128,648622610,648622987⟩]
theorem checked20106 : checkPrefixCuts (2^48) 2639265793 9 Manual.Count131072.C020106.packed 128 cuts20106 = true := by
 decide +kernel
def pointBounds20106 : List (Nat × Nat × Nat) := [(2639319040,100089576145363,100089956555424)]
theorem point_links_checked20106 : (cuts20106.take 1).map (fun c => (2639265793-1+2*2^9*c.k,100089319337334+c.lower,100089699747247+c.upper)) = pointBounds20106 := by
 decide +kernel
def cuts20107 : List PrefixCut := [⟨5,26874173,26874189⟩,
⟨86,434565566,434565820⟩,
⟨128,644218241,644218621⟩]
theorem checked20107 : checkPrefixCuts (2^48) 2639396865 9 Manual.Count131072.C020107.packed 128 cuts20107 = true := by
 decide +kernel
def pointBounds20107 : List (Nat × Nat × Nat) := [(2639401984,100089994834117,100090375244423),(2639484928,100090402525510,100090782936054)]
theorem point_links_checked20107 : (cuts20107.take 2).map (fun c => (2639396865-1+2*2^9*c.k,100089967959944+c.lower,100090348370234+c.upper)) = pointBounds20107 := by
 decide +kernel
def cuts20108 : List PrefixCut := [⟨39,197066181,197066298⟩,
⟨120,609530635,609530988⟩,
⟨128,650584424,650584800⟩]
theorem checked20108 : checkPrefixCuts (2^48) 2639527937 9 Manual.Count131072.C020108.packed 128 cuts20108 = true := by
 decide +kernel
def pointBounds20108 : List (Nat × Nat × Nat) := [(2639567872,100090809244366,100091189655153),(2639650816,100091221708820,100091602119843)]
theorem point_links_checked20108 : (cuts20108.take 2).map (fun c => (2639527937-1+2*2^9*c.k,100090612178185+c.lower,100090992588855+c.upper)) = pointBounds20108 := by
 decide +kernel
def cuts20109 : List PrefixCut := [⟨73,363613496,363613712⟩,
⟨128,636796685,636797063⟩]
theorem checked20109 : checkPrefixCuts (2^48) 2639659009 9 Manual.Count131072.C020109.packed 128 cuts20109 = true := by
 decide +kernel
def pointBounds20109 : List (Nat × Nat × Nat) := [(2639733760,100091626376105,100092006787367)]
theorem point_links_checked20109 : (cuts20109.take 1).map (fun c => (2639659009-1+2*2^9*c.k,100091262762609+c.lower,100091643173655+c.upper)) = pointBounds20109 := by
 decide +kernel
def cuts20110 : List PrefixCut := [⟨26,131364734,131364810⟩,
⟨107,541337838,541338165⟩,
⟨128,650199814,650200203⟩]
theorem checked20110 : checkPrefixCuts (2^48) 2639790081 9 Manual.Count131072.C020110.packed 128 cuts20110 = true := by
 decide +kernel
def pointBounds20110 : List (Nat × Nat × Nat) := [(2639816704,100092030924028,100092411335528),(2639899648,100092440897132,100092821308883)]
theorem point_links_checked20110 : (cuts20110.take 2).map (fun c => (2639790081-1+2*2^9*c.k,100091899559294+c.lower,100092279970718+c.upper)) = pointBounds20110 := by
 decide +kernel
def cuts20111 : List PrefixCut := [⟨60,303870484,303870661⟩,
⟨128,648461712,648462090⟩]
theorem checked20111 : checkPrefixCuts (2^48) 2639921153 9 Manual.Count131072.C020111.packed 128 cuts20111 = true := by
 decide +kernel
def pointBounds20111 : List (Nat × Nat × Nat) := [(2639982592,100092853629592,100093234041582)]
theorem point_links_checked20111 : (cuts20111.take 1).map (fun c => (2639921153-1+2*2^9*c.k,100092549759108+c.lower,100092930170921+c.upper)) = pointBounds20111 := by
 decide +kernel
def cuts20112 : List PrefixCut := [⟨13,64716459,64716497⟩,
⟨94,481794190,481794469⟩,
⟨128,645551118,645551497⟩]
theorem checked20112 : checkPrefixCuts (2^48) 2640052225 9 Manual.Count131072.C020112.packed 128 cuts20112 = true := by
 decide +kernel
def pointBounds20112 : List (Nat × Nat × Nat) := [(2640065536,100093262937279,100093643349508),(2640148480,100093680015010,100094060427480)]
theorem point_links_checked20112 : (cuts20112.take 2).map (fun c => (2640052225-1+2*2^9*c.k,100093198220820+c.lower,100093578633011+c.upper)) = pointBounds20112 := by
 decide +kernel
def cuts20113 : List PrefixCut := [⟨47,230705989,230706127⟩,
⟨128,638695784,638696167⟩]
theorem checked20113 : checkPrefixCuts (2^48) 2640183297 9 Manual.Count131072.C020113.packed 128 cuts20113 = true := by
 decide +kernel
def pointBounds20113 : List (Nat × Nat × Nat) := [(2640231424,100094074477927,100094454890635),(2640314368,100094482467722,100094862880675)]
theorem point_links_checked20113 : (cuts20113.take 2).map (fun c => (2640183297-1+2*2^9*c.k,100093843771938+c.lower,100094224184508+c.upper)) = pointBounds20113 := by
 decide +kernel
def cuts20114 : List PrefixCut := [⟨81,409042956,409043193⟩,
⟨128,645593374,645593746⟩]
theorem checked20114 : checkPrefixCuts (2^48) 2640314369 9 Manual.Count131072.C020114.packed 128 cuts20114 = true := by
 decide +kernel
def pointBounds20114 : List (Nat × Nat × Nat) := [(2640397312,100094891510678,100095271923868)]
theorem point_links_checked20114 : (cuts20114.take 1).map (fun c => (2640314369-1+2*2^9*c.k,100094482467722+c.lower,100094862880675+c.upper)) = pointBounds20114 := by
 decide +kernel
def cuts20115 : List PrefixCut := [⟨34,165763930,165764026⟩,
⟨115,574461486,574461822⟩,
⟨128,642256713,642257090⟩]
theorem checked20115 : checkPrefixCuts (2^48) 2640445441 9 Manual.Count131072.C020115.packed 128 cuts20115 = true := by
 decide +kernel
def pointBounds20115 : List (Nat × Nat × Nat) := [(2640480256,100095293825026,100095674238447),(2640563200,100095702522582,100096082936243)]
theorem point_links_checked20115 : (cuts20115.take 2).map (fun c => (2640445441-1+2*2^9*c.k,100095128061096+c.lower,100095508474421+c.upper)) = pointBounds20115 := by
 decide +kernel
def cuts20116 : List PrefixCut := [⟨68,341848837,341849039⟩,
⟨128,642331516,642331893⟩]
theorem checked20116 : checkPrefixCuts (2^48) 2640576513 9 Manual.Count131072.C020116.packed 128 cuts20116 = true := by
 decide +kernel
def pointBounds20116 : List (Nat × Nat × Nat) := [(2640646144,100096112166646,100096492580550)]
theorem point_links_checked20116 : (cuts20116.take 1).map (fun c => (2640576513-1+2*2^9*c.k,100095770317809+c.lower,100096150731511+c.upper)) = pointBounds20116 := by
 decide +kernel
def cuts20117 : List PrefixCut := [⟨21,105844129,105844189⟩,
⟨102,508534210,508534506⟩,
⟨128,640913972,640914346⟩]
theorem checked20117 : checkPrefixCuts (2^48) 2640707585 9 Manual.Count131072.C020117.packed 128 cuts20117 = true := by
 decide +kernel
def pointBounds20117 : List (Nat × Nat × Nat) := [(2640729088,100096518493454,100096898907593),(2640812032,100096921183535,100097301597910)]
theorem point_links_checked20117 : (cuts20117.take 2).map (fun c => (2640707585-1+2*2^9*c.k,100096412649325+c.lower,100096793063404+c.upper)) = pointBounds20117 := by
 decide +kernel
def cuts20118 : List PrefixCut := [⟨55,280423249,280423412⟩,
⟨128,645998228,645998604⟩]
theorem checked20118 : checkPrefixCuts (2^48) 2640838657 9 Manual.Count131072.C020118.packed 128 cuts20118 = true := by
 decide +kernel
def pointBounds20118 : List (Nat × Nat × Nat) := [(2640894976,100097333986546,100097714401162)]
theorem point_links_checked20118 : (cuts20118.take 1).map (fun c => (2640838657-1+2*2^9*c.k,100097053563297+c.lower,100097433977750+c.upper)) = pointBounds20118 := by
 decide +kernel
def cuts20119 : List PrefixCut := [⟨8,38688524,38688548⟩,
⟨89,443472222,443472487⟩,
⟨128,639997715,639998095⟩]
theorem checked20119 : checkPrefixCuts (2^48) 2640969729 9 Manual.Count131072.C020119.packed 128 cuts20119 = true := by
 decide +kernel
def pointBounds20119 : List (Nat × Nat × Nat) := [(2640977920,100097738250049,100098118664902),(2641060864,100098143033747,100098523448841)]
theorem point_links_checked20119 : (cuts20119.take 2).map (fun c => (2640969729-1+2*2^9*c.k,100097699561525+c.lower,100098079976354+c.upper)) = pointBounds20119 := by
 decide +kernel
def cuts20120 : List PrefixCut := [⟨42,210696740,210696860⟩,
⟨123,616947045,616947405⟩,
⟨128,643163181,643163556⟩]
theorem checked20120 : checkPrefixCuts (2^48) 2641100801 9 Manual.Count131072.C020120.packed 128 cuts20120 = true := by
 decide +kernel
def pointBounds20120 : List (Nat × Nat × Nat) := [(2641143808,100098550255980,100098930671309),(2641226752,100098956506285,100099336921854)]
theorem point_links_checked20120 : (cuts20120.take 2).map (fun c => (2641100801-1+2*2^9*c.k,100098339559240+c.lower,100098719974449+c.upper)) = pointBounds20120 := by
 decide +kernel
def cuts20121 : List PrefixCut := [⟨76,380554283,380554506⟩,
⟨128,644196914,644197287⟩]
theorem checked20121 : checkPrefixCuts (2^48) 2641231873 9 Manual.Count131072.C020121.packed 128 cuts20121 = true := by
 decide +kernel
def pointBounds20121 : List (Nat × Nat × Nat) := [(2641309696,100099363276704,100099743692511)]
theorem point_links_checked20121 : (cuts20121.take 1).map (fun c => (2641231873-1+2*2^9*c.k,100098982722421+c.lower,100099363138005+c.upper)) = pointBounds20121 := by
 decide +kernel
def cuts20122 : List PrefixCut := [⟨29,147910356,147910440⟩,
⟨110,554015831,554016152⟩,
⟨128,646083108,646083484⟩]
theorem checked20122 : checkPrefixCuts (2^48) 2641362945 9 Manual.Count131072.C020122.packed 128 cuts20122 = true := by
 decide +kernel
def pointBounds20122 : List (Nat × Nat × Nat) := [(2641392640,100099774829691,100100155245732),(2641475584,100100180935166,100100561351444)]
theorem point_links_checked20122 : (cuts20122.take 2).map (fun c => (2641362945-1+2*2^9*c.k,100099626919335+c.lower,100100007335292+c.upper)) = pointBounds20122 := by
 decide +kernel
def cuts20123 : List PrefixCut := [⟨63,313705808,313705987⟩,
⟨128,650313126,650313495⟩]
theorem checked20123 : checkPrefixCuts (2^48) 2641494017 9 Manual.Count131072.C020123.packed 128 cuts20123 = true := by
 decide +kernel
def pointBounds20123 : List (Nat × Nat × Nat) := [(2641558528,100100586708251,100100967124763)]
theorem point_links_checked20123 : (cuts20123.take 1).map (fun c => (2641494017-1+2*2^9*c.k,100100273002443+c.lower,100100653418776+c.upper)) = pointBounds20123 := by
 decide +kernel
def cuts20124 : List PrefixCut := [⟨16,79062590,79062639⟩,
⟨97,487260778,487261072⟩,
⟨128,641543787,641544171⟩]
theorem checked20124 : checkPrefixCuts (2^48) 2641625089 9 Manual.Count131072.C020124.packed 128 cuts20124 = true := by
 decide +kernel
def pointBounds20124 : List (Nat × Nat × Nat) := [(2641641472,100101002378159,100101382794910),(2641724416,100101410576347,100101790993343)]
theorem point_links_checked20124 : (cuts20124.take 2).map (fun c => (2641625089-1+2*2^9*c.k,100100923315569+c.lower,100101303732271+c.upper)) = pointBounds20124 := by
 decide +kernel
def cuts20125 : List PrefixCut := [⟨50,256992237,256992389⟩,
⟨128,643003767,643004144⟩]
theorem checked20125 : checkPrefixCuts (2^48) 2641756161 9 Manual.Count131072.C020125.packed 128 cuts20125 = true := by
 decide +kernel
def pointBounds20125 : List (Nat × Nat × Nat) := [(2641807360,100101821851593,100102202268831)]
theorem point_links_checked20125 : (cuts20125.take 1).map (fun c => (2641756161-1+2*2^9*c.k,100101564859356+c.lower,100101945276442+c.upper)) = pointBounds20125 := by
 decide +kernel
def cuts20126 : List PrefixCut := [⟨3,15342200,15342209⟩,
⟨84,422969262,422969508⟩,
⟨128,641799825,641800197⟩]
theorem checked20126 : checkPrefixCuts (2^48) 2641887233 9 Manual.Count131072.C020126.packed 128 cuts20126 = true := by
 decide +kernel
def pointBounds20126 : List (Nat × Nat × Nat) := [(2641890304,100102223205323,100102603622795),(2641973248,100102630832385,100103011250094)]
theorem point_links_checked20126 : (cuts20126.take 2).map (fun c => (2641887233-1+2*2^9*c.k,100102207863123+c.lower,100102588280586+c.upper)) = pointBounds20126 := by
 decide +kernel
def cuts20127 : List PrefixCut := [⟨37,187292146,187292258⟩,
⟨118,594787066,594787419⟩,
⟨128,645603188,645603570⟩]
theorem checked20127 : checkPrefixCuts (2^48) 2642018305 9 Manual.Count131072.C020127.packed 128 cuts20127 = true := by
 decide +kernel
def pointBounds20127 : List (Nat × Nat × Nat) := [(2642056192,100103036955094,100103417373041),(2642139136,100103444450014,100103824868202)]
theorem point_links_checked20127 : (cuts20127.take 2).map (fun c => (2642018305-1+2*2^9*c.k,100102849662948+c.lower,100103230080783+c.upper)) = pointBounds20127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000003
