import PlattAssemblyKernel
import PlattCertificates.Count131072.C020064
import PlattCertificates.Count131072.C020065
import PlattCertificates.Count131072.C020066
import PlattCertificates.Count131072.C020067
import PlattCertificates.Count131072.C020068
import PlattCertificates.Count131072.C020069
import PlattCertificates.Count131072.C020070
import PlattCertificates.Count131072.C020071
import PlattCertificates.Count131072.C020072
import PlattCertificates.Count131072.C020073
import PlattCertificates.Count131072.C020074
import PlattCertificates.Count131072.C020075
import PlattCertificates.Count131072.C020076
import PlattCertificates.Count131072.C020077
import PlattCertificates.Count131072.C020078
import PlattCertificates.Count131072.C020079
import PlattCertificates.Count131072.C020080
import PlattCertificates.Count131072.C020081
import PlattCertificates.Count131072.C020082
import PlattCertificates.Count131072.C020083
import PlattCertificates.Count131072.C020084
import PlattCertificates.Count131072.C020085
import PlattCertificates.Count131072.C020086
import PlattCertificates.Count131072.C020087
import PlattCertificates.Count131072.C020088
import PlattCertificates.Count131072.C020089
import PlattCertificates.Count131072.C020090
import PlattCertificates.Count131072.C020091
import PlattCertificates.Count131072.C020092
import PlattCertificates.Count131072.C020093
import PlattCertificates.Count131072.C020094
import PlattCertificates.Count131072.C020095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20064 : List PrefixCut := [⟨1,5343592,5343595⟩,
⟨82,411022623,411022867⟩,
⟨128,642070132,642070516⟩]
theorem checked20064 : checkPrefixCuts (2^48) 2633760769 9 Manual.Count131072.C020064.packed 128 cuts20064 = true := by
 decide +kernel
def pointBounds20064 : List (Nat × Nat × Nat) := [(2633761792,100062287855108,100062668249151),(2633844736,100062693534139,100063073928423)]
theorem point_links_checked20064 : (cuts20064.take 2).map (fun c => (2633760769-1+2*2^9*c.k,100062282511516+c.lower,100062662905556+c.upper)) = pointBounds20064 := by
 decide +kernel
def cuts20065 : List PrefixCut := [⟨35,180282604,180282705⟩,
⟨116,586897800,586898143⟩,
⟨128,647488250,647488626⟩]
theorem checked20065 : checkPrefixCuts (2^48) 2633891841 9 Manual.Count131072.C020065.packed 128 cuts20065 = true := by
 decide +kernel
def pointBounds20065 : List (Nat × Nat × Nat) := [(2633927680,100063104864252,100063485258777),(2634010624,100063511479448,100063891874215)]
theorem point_links_checked20065 : (cuts20065.take 2).map (fun c => (2633891841-1+2*2^9*c.k,100062924581648+c.lower,100063304976072+c.upper)) = pointBounds20065 := by
 decide +kernel
def cuts20066 : List PrefixCut := [⟨69,346653128,346653331⟩,
⟨128,645639358,645639739⟩]
theorem checked20066 : checkPrefixCuts (2^48) 2634022913 9 Manual.Count131072.C020066.packed 128 cuts20066 = true := by
 decide +kernel
def pointBounds20066 : List (Nat × Nat × Nat) := [(2634093568,100063918723026,100064299118029)]
theorem point_links_checked20066 : (cuts20066.take 1).map (fun c => (2634022913-1+2*2^9*c.k,100063572069898+c.lower,100063952464698+c.upper)) = pointBounds20066 := by
 decide +kernel
def cuts20067 : List PrefixCut := [⟨22,111663937,111664005⟩,
⟨103,516958587,516958890⟩,
⟨128,644645667,644646045⟩]
theorem checked20067 : checkPrefixCuts (2^48) 2634153985 9 Manual.Count131072.C020067.packed 128 cuts20067 = true := by
 decide +kernel
def pointBounds20067 : List (Nat × Nat × Nat) := [(2634176512,100064329373193,100064709768442),(2634259456,100064734667843,100065115063327)]
theorem point_links_checked20067 : (cuts20067.take 2).map (fun c => (2634153985-1+2*2^9*c.k,100064217709256+c.lower,100064598104437+c.upper)) = pointBounds20067 := by
 decide +kernel
def cuts20068 : List PrefixCut := [⟨56,280800272,280800441⟩,
⟨128,642476498,642476876⟩]
theorem checked20068 : checkPrefixCuts (2^48) 2634285057 9 Manual.Count131072.C020068.packed 128 cuts20068 = true := by
 decide +kernel
def pointBounds20068 : List (Nat × Nat × Nat) := [(2634342400,100065143155195,100065523550923)]
theorem point_links_checked20068 : (cuts20068.take 1).map (fun c => (2634285057-1+2*2^9*c.k,100064862354923+c.lower,100065242750482+c.upper)) = pointBounds20068 := by
 decide +kernel
def cuts20069 : List PrefixCut := [⟨9,43699637,43699662⟩,
⟨90,449276375,449276635⟩,
⟨128,645435971,645436346⟩]
theorem checked20069 : checkPrefixCuts (2^48) 2634416129 9 Manual.Count131072.C020069.packed 128 cuts20069 = true := by
 decide +kernel
def pointBounds20069 : List (Nat × Nat × Nat) := [(2634425344,100065548531058,100065928927020),(2634508288,100065954107796,100066334503993)]
theorem point_links_checked20069 : (cuts20069.take 2).map (fun c => (2634416129-1+2*2^9*c.k,100065504831421+c.lower,100065885227358+c.upper)) = pointBounds20069 := by
 decide +kernel
def cuts20070 : List PrefixCut := [⟨43,214960183,214960310⟩,
⟨124,619336270,619336631⟩,
⟨128,640169040,640169412⟩]
theorem checked20070 : checkPrefixCuts (2^48) 2634547201 9 Manual.Count131072.C020070.packed 128 cuts20070 = true := by
 decide +kernel
def pointBounds20070 : List (Nat × Nat × Nat) := [(2634591232,100066365227575,100066745624014),(2634674176,100066769603662,100067150000335)]
theorem point_links_checked20070 : (cuts20070.take 2).map (fun c => (2634547201-1+2*2^9*c.k,100066150267392+c.lower,100066530663704+c.upper)) = pointBounds20070 := by
 decide +kernel
def cuts20071 : List PrefixCut := [⟨77,390688471,390688702⟩,
⟨128,650713617,650713999⟩]
theorem checked20071 : checkPrefixCuts (2^48) 2634678273 9 Manual.Count131072.C020071.packed 128 cuts20071 = true := by
 decide +kernel
def pointBounds20071 : List (Nat × Nat × Nat) := [(2634757120,100067181124903,100067561521818)]
theorem point_links_checked20071 : (cuts20071.take 1).map (fun c => (2634678273-1+2*2^9*c.k,100066790436432+c.lower,100067170833116+c.upper)) = pointBounds20071 := by
 decide +kernel
def cuts20072 : List PrefixCut := [⟨30,148812375,148812464⟩,
⟨111,551761483,551761811⟩,
⟨128,637007317,637007692⟩]
theorem checked20072 : checkPrefixCuts (2^48) 2634809345 9 Manual.Count131072.C020072.packed 128 cuts20072 = true := by
 decide +kernel
def pointBounds20072 : List (Nat × Nat × Nat) := [(2634840064,100067589962424,100067970359579),(2634923008,100067992911532,100068373308926)]
theorem point_links_checked20072 : (cuts20072.take 2).map (fun c => (2634809345-1+2*2^9*c.k,100067441150049+c.lower,100067821547115+c.upper)) = pointBounds20072 := by
 decide +kernel
def cuts20073 : List PrefixCut := [⟨64,322604546,322604736⟩,
⟨128,644239630,644240013⟩]
theorem checked20073 : checkPrefixCuts (2^48) 2634940417 9 Manual.Count131072.C020073.packed 128 cuts20073 = true := by
 decide +kernel
def pointBounds20073 : List (Nat × Nat × Nat) := [(2635005952,100068400761912,100068781159543)]
theorem point_links_checked20073 : (cuts20073.take 1).map (fun c => (2634940417-1+2*2^9*c.k,100068078157366+c.lower,100068458554807+c.upper)) = pointBounds20073 := by
 decide +kernel
def cuts20074 : List PrefixCut := [⟨17,84920581,84920632⟩,
⟨98,491463494,491463786⟩,
⟨128,644741595,644741976⟩]
theorem checked20074 : checkPrefixCuts (2^48) 2635071489 9 Manual.Count131072.C020074.packed 128 cuts20074 = true := by
 decide +kernel
def pointBounds20074 : List (Nat × Nat × Nat) := [(2635088896,100068807317577,100069187715452),(2635171840,100069213860490,100069594258606)]
theorem point_links_checked20074 : (cuts20074.take 2).map (fun c => (2635071489-1+2*2^9*c.k,100068722396996+c.lower,100069102794820+c.upper)) = pointBounds20074 := by
 decide +kernel
def cuts20075 : List PrefixCut := [⟨51,255174633,255174781⟩,
⟨128,642039199,642039567⟩]
theorem checked20075 : checkPrefixCuts (2^48) 2635202561 9 Manual.Count131072.C020075.packed 128 cuts20075 = true := by
 decide +kernel
def pointBounds20075 : List (Nat × Nat × Nat) := [(2635254784,100069622313224,100070002711577)]
theorem point_links_checked20075 : (cuts20075.take 1).map (fun c => (2635202561-1+2*2^9*c.k,100069367138591+c.lower,100069747536796+c.upper)) = pointBounds20075 := by
 decide +kernel
def cuts20076 : List PrefixCut := [⟨4,19332245,19332257⟩,
⟨85,418894338,418894582⟩,
⟨128,631860819,631861191⟩]
theorem checked20076 : checkPrefixCuts (2^48) 2635333633 9 Manual.Count131072.C020076.packed 128 cuts20076 = true := by
 decide +kernel
def pointBounds20076 : List (Nat × Nat × Nat) := [(2635337728,100070028510035,100070408908620),(2635420672,100070428072128,100070808470945)]
theorem point_links_checked20076 : (cuts20076.take 2).map (fun c => (2635333633-1+2*2^9*c.k,100070009177790+c.lower,100070389576363+c.upper)) = pointBounds20076 := by
 decide +kernel
def cuts20077 : List PrefixCut := [⟨38,190641511,190641624⟩,
⟨119,598508750,598509103⟩,
⟨128,645286113,645286493⟩]
theorem checked20077 : checkPrefixCuts (2^48) 2635464705 9 Manual.Count131072.C020077.packed 128 cuts20077 = true := by
 decide +kernel
def pointBounds20077 : List (Nat × Nat × Nat) := [(2635503616,100070831680120,100071212079178),(2635586560,100071239547359,100071619946657)]
theorem point_links_checked20077 : (cuts20077.take 2).map (fun c => (2635464705-1+2*2^9*c.k,100070641038609+c.lower,100071021437554+c.upper)) = pointBounds20077 := by
 decide +kernel
def cuts20078 : List PrefixCut := [⟨72,367805246,367805459⟩,
⟨128,640341757,640342130⟩]
theorem checked20078 : checkPrefixCuts (2^48) 2635595777 9 Manual.Count131072.C020078.packed 128 cuts20078 = true := by
 decide +kernel
def pointBounds20078 : List (Nat × Nat × Nat) := [(2635669504,100071654129968,100072034529506)]
theorem point_links_checked20078 : (cuts20078.take 1).map (fun c => (2635595777-1+2*2^9*c.k,100071286324722+c.lower,100071666724047+c.upper)) = pointBounds20078 := by
 decide +kernel
def cuts20079 : List PrefixCut := [⟨25,131033298,131033377⟩,
⟨106,536512680,536513001⟩,
⟨128,644794980,644795366⟩]
theorem checked20079 : checkPrefixCuts (2^48) 2635726849 9 Manual.Count131072.C020079.packed 128 cuts20079 = true := by
 decide +kernel
def pointBounds20079 : List (Nat × Nat × Nat) := [(2635752448,100072057699777,100072438099554),(2635835392,100072463179159,100072843579178)]
theorem point_links_checked20079 : (cuts20079.take 2).map (fun c => (2635726849-1+2*2^9*c.k,100071926666479+c.lower,100072307066177+c.upper)) = pointBounds20079 := by
 decide +kernel
def cuts20080 : List PrefixCut := [⟨59,302416826,302417001⟩,
⟨128,645723948,645724329⟩]
theorem checked20080 : checkPrefixCuts (2^48) 2635857921 9 Manual.Count131072.C020080.packed 128 cuts20080 = true := by
 decide +kernel
def pointBounds20080 : List (Nat × Nat × Nat) := [(2635918336,100072873878285,100073254278544)]
theorem point_links_checked20080 : (cuts20080.take 1).map (fun c => (2635857921-1+2*2^9*c.k,100072571461459+c.lower,100072951861543+c.upper)) = pointBounds20080 := by
 decide +kernel
def cuts20081 : List PrefixCut := [⟨12,59050039,59050073⟩,
⟨93,467587811,467588086⟩,
⟨128,645051067,645051445⟩]
theorem checked20081 : checkPrefixCuts (2^48) 2635988993 9 Manual.Count131072.C020081.packed 128 cuts20081 = true := by
 decide +kernel
def pointBounds20081 : List (Nat × Nat × Nat) := [(2636001280,100073276235446,100073656635945),(2636084224,100073684773218,100074065173958)]
theorem point_links_checked20081 : (cuts20081.take 2).map (fun c => (2635988993-1+2*2^9*c.k,100073217185407+c.lower,100073597585872+c.upper)) = pointBounds20081 := by
 decide +kernel
def cuts20082 : List PrefixCut := [⟨46,229032914,229033051⟩,
⟨127,635943298,635943674⟩,
⟨128,639359967,639360345⟩]
theorem checked20082 : checkPrefixCuts (2^48) 2636120065 9 Manual.Count131072.C020082.packed 128 cuts20082 = true := by
 decide +kernel
def pointBounds20082 : List (Nat × Nat × Nat) := [(2636167168,100074091269388,100074471670368),(2636250112,100074498179772,100074878580991)]
theorem point_links_checked20082 : (cuts20082.take 2).map (fun c => (2636120065-1+2*2^9*c.k,100073862236474+c.lower,100074242637317+c.upper)) = pointBounds20082 := by
 decide +kernel
def cuts20083 : List PrefixCut := [⟨80,393017573,393017802⟩,
⟨128,639755139,639755511⟩]
theorem checked20083 : checkPrefixCuts (2^48) 2636251137 9 Manual.Count131072.C020083.packed 128 cuts20083 = true := by
 decide +kernel
def pointBounds20083 : List (Nat × Nat × Nat) := [(2636333056,100074894614014,100075275015464)]
theorem point_links_checked20083 : (cuts20083.take 1).map (fun c => (2636251137-1+2*2^9*c.k,100074501596441+c.lower,100074881997662+c.upper)) = pointBounds20083 := by
 decide +kernel
def cuts20084 : List PrefixCut := [⟨33,166232940,166233041⟩,
⟨114,578870117,578870461⟩,
⟨128,651360539,651360927⟩]
theorem checked20084 : checkPrefixCuts (2^48) 2636382209 9 Manual.Count131072.C020084.packed 128 cuts20084 = true := by
 decide +kernel
def pointBounds20084 : List (Nat × Nat × Nat) := [(2636416000,100075307584520,100075687986214),(2636498944,100075720221697,100076100623634)]
theorem point_links_checked20084 : (cuts20084.take 2).map (fun c => (2636382209-1+2*2^9*c.k,100075141351580+c.lower,100075521753173+c.upper)) = pointBounds20084 := by
 decide +kernel
def cuts20085 : List PrefixCut := [⟨67,337144588,337144790⟩,
⟨128,638410691,638411072⟩]
theorem checked20085 : checkPrefixCuts (2^48) 2636513281 9 Manual.Count131072.C020085.packed 128 cuts20085 = true := by
 decide +kernel
def pointBounds20085 : List (Nat × Nat × Nat) := [(2636581888,100076129856707,100076510258890)]
theorem point_links_checked20085 : (cuts20085.take 1).map (fun c => (2636513281-1+2*2^9*c.k,100075792712119+c.lower,100076173114100+c.upper)) = pointBounds20085 := by
 decide +kernel
def cuts20086 : List PrefixCut := [⟨20,101416826,101416885⟩,
⟨101,506755906,506756202⟩,
⟨128,646598707,646599081⟩]
theorem checked20086 : checkPrefixCuts (2^48) 2636644353 9 Manual.Count131072.C020086.packed 128 cuts20086 = true := by
 decide +kernel
def pointBounds20086 : List (Nat × Nat × Nat) := [(2636664832,100076532539636,100076912942057),(2636747776,100076937878716,100077318281374)]
theorem point_links_checked20086 : (cuts20086.take 2).map (fun c => (2636644353-1+2*2^9*c.k,100076431122810+c.lower,100076811525172+c.upper)) = pointBounds20086 := by
 decide +kernel
def cuts20087 : List PrefixCut := [⟨54,265376867,265377025⟩,
⟨128,634290686,634291063⟩]
theorem checked20087 : checkPrefixCuts (2^48) 2636775425 9 Manual.Count131072.C020087.packed 128 cuts20087 = true := by
 decide +kernel
def pointBounds20087 : List (Nat × Nat × Nat) := [(2636830720,100077343098384,100077723501278)]
theorem point_links_checked20087 : (cuts20087.take 1).map (fun c => (2636775425-1+2*2^9*c.k,100077077721517+c.lower,100077458124253+c.upper)) = pointBounds20087 := by
 decide +kernel
def cuts20088 : List PrefixCut := [⟨7,32983965,32983986⟩,
⟨88,443195010,443195269⟩,
⟨128,648562534,648562911⟩]
theorem checked20088 : checkPrefixCuts (2^48) 2636906497 9 Manual.Count131072.C020088.packed 128 cuts20088 = true := by
 decide +kernel
def pointBounds20088 : List (Nat × Nat × Nat) := [(2636913664,100077744996168,100078125399302),(2636996608,100078155207213,100078535610585)]
theorem point_links_checked20088 : (cuts20088.take 2).map (fun c => (2636906497-1+2*2^9*c.k,100077712012203+c.lower,100078092415316+c.upper)) = pointBounds20088 := by
 decide +kernel
def cuts20089 : List PrefixCut := [⟨41,207178864,207178985⟩,
⟨122,620672846,620673202⟩,
⟨128,650238130,650238502⟩]
theorem checked20089 : checkPrefixCuts (2^48) 2637037569 9 Manual.Count131072.C020089.packed 128 cuts20089 = true := by
 decide +kernel
def pointBounds20089 : List (Nat × Nat × Nat) := [(2637079552,100078567753601,100078948157212),(2637162496,100078981247583,100079361651429)]
theorem point_links_checked20089 : (cuts20089.take 2).map (fun c => (2637037569-1+2*2^9*c.k,100078360574737+c.lower,100078740978227+c.upper)) = pointBounds20089 := by
 decide +kernel
def cuts20090 : List PrefixCut := [⟨75,380713712,380713933⟩,
⟨128,646897178,646897559⟩]
theorem checked20090 : checkPrefixCuts (2^48) 2637168641 9 Manual.Count131072.C020090.packed 128 cuts20090 = true := by
 decide +kernel
def pointBounds20090 : List (Nat × Nat × Nat) := [(2637245440,100079391526579,100079771930662)]
theorem point_links_checked20090 : (cuts20090.take 1).map (fun c => (2637168641-1+2*2^9*c.k,100079010812867+c.lower,100079391216729+c.upper)) = pointBounds20090 := by
 decide +kernel
def cuts20091 : List PrefixCut := [⟨28,138212579,138212663⟩,
⟨109,546331350,546331670⟩,
⟨128,643343052,643343429⟩]
theorem checked20091 : checkPrefixCuts (2^48) 2637299713 9 Manual.Count131072.C020091.packed 128 cuts20091 = true := by
 decide +kernel
def pointBounds20091 : List (Nat × Nat × Nat) := [(2637328384,100079795922624,100080176326951),(2637411328,100080204041395,100080584445958)]
theorem point_links_checked20091 : (cuts20091.take 2).map (fun c => (2637299713-1+2*2^9*c.k,100079657710045+c.lower,100080038114288+c.upper)) = pointBounds20091 := by
 decide +kernel
def cuts20092 : List PrefixCut := [⟨62,315683215,315683401⟩,
⟨128,646512739,646513122⟩]
theorem checked20092 : checkPrefixCuts (2^48) 2637430785 9 Manual.Count131072.C020092.packed 128 cuts20092 = true := by
 decide +kernel
def pointBounds20092 : List (Nat × Nat × Nat) := [(2637494272,100080616736312,100080997141118)]
theorem point_links_checked20092 : (cuts20092.take 1).map (fun c => (2637430785-1+2*2^9*c.k,100080301053097+c.lower,100080681457717+c.upper)) = pointBounds20092 := by
 decide +kernel
def cuts20093 : List PrefixCut := [⟨15,76729902,76729946⟩,
⟨96,481715363,481715647⟩,
⟨128,639330748,639331123⟩]
theorem checked20093 : checkPrefixCuts (2^48) 2637561857 9 Manual.Count131072.C020093.packed 128 cuts20093 = true := by
 decide +kernel
def pointBounds20093 : List (Nat × Nat × Nat) := [(2637577216,100081024295738,100081404700785),(2637660160,100081429281199,100081809686486)]
theorem point_links_checked20093 : (cuts20093.take 2).map (fun c => (2637561857-1+2*2^9*c.k,100080947565836+c.lower,100081327970839+c.upper)) = pointBounds20093 := by
 decide +kernel
def cuts20094 : List PrefixCut := [⟨49,245863337,245863482⟩,
⟨128,647195369,647195754⟩]
theorem checked20094 : checkPrefixCuts (2^48) 2637692929 9 Manual.Count131072.C020094.packed 128 cuts20094 = true := by
 decide +kernel
def pointBounds20094 : List (Nat × Nat × Nat) := [(2637743104,100081832759921,100082213165444)]
theorem point_links_checked20094 : (cuts20094.take 1).map (fun c => (2637692929-1+2*2^9*c.k,100081586896584+c.lower,100081967301962+c.upper)) = pointBounds20094 := by
 decide +kernel
def cuts20095 : List PrefixCut := [⟨2,9817061,9817066⟩,
⟨83,416685069,416685312⟩,
⟨128,645349292,645349668⟩]
theorem checked20095 : checkPrefixCuts (2^48) 2637824001 9 Manual.Count131072.C020095.packed 128 cuts20095 = true := by
 decide +kernel
def pointBounds20095 : List (Nat × Nat × Nat) := [(2637826048,100082243909014,100082624314782),(2637908992,100082650777022,100083031183028)]
theorem point_links_checked20095 : (cuts20095.take 2).map (fun c => (2637824001-1+2*2^9*c.k,100082234091953+c.lower,100082614497716+c.upper)) = pointBounds20095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000002
