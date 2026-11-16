import PlattAssemblyKernel
import PlattCertificates.Count131072.C020000
import PlattCertificates.Count131072.C020001
import PlattCertificates.Count131072.C020002
import PlattCertificates.Count131072.C020003
import PlattCertificates.Count131072.C020004
import PlattCertificates.Count131072.C020005
import PlattCertificates.Count131072.C020006
import PlattCertificates.Count131072.C020007
import PlattCertificates.Count131072.C020008
import PlattCertificates.Count131072.C020009
import PlattCertificates.Count131072.C020010
import PlattCertificates.Count131072.C020011
import PlattCertificates.Count131072.C020012
import PlattCertificates.Count131072.C020013
import PlattCertificates.Count131072.C020014
import PlattCertificates.Count131072.C020015
import PlattCertificates.Count131072.C020016
import PlattCertificates.Count131072.C020017
import PlattCertificates.Count131072.C020018
import PlattCertificates.Count131072.C020019
import PlattCertificates.Count131072.C020020
import PlattCertificates.Count131072.C020021
import PlattCertificates.Count131072.C020022
import PlattCertificates.Count131072.C020023
import PlattCertificates.Count131072.C020024
import PlattCertificates.Count131072.C020025
import PlattCertificates.Count131072.C020026
import PlattCertificates.Count131072.C020027
import PlattCertificates.Count131072.C020028
import PlattCertificates.Count131072.C020029
import PlattCertificates.Count131072.C020030
import PlattCertificates.Count131072.C020031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20000 : List PrefixCut := [⟨12,56930145,56930178⟩,
⟨93,466798261,466798531⟩,
⟨128,648409786,648410165⟩]
theorem checked20000 : checkPrefixCuts (2^48) 2625372161 9 Manual.Count131072.C020000.packed 128 cuts20000 = true := by
 decide +kernel
def pointBounds20000 : List (Nat × Nat × Nat) := [(2625384448,100020930216157,100021310585943),(2625467392,100021340084273,100021720454296)]
theorem point_links_checked20000 : (cuts20000.take 2).map (fun c => (2625372161-1+2*2^9*c.k,100020873286012+c.lower,100021253655765+c.upper)) = pointBounds20000 := by
 decide +kernel
def cuts20001 : List PrefixCut := [⟨46,235426615,235426751⟩,
⟨127,643231982,643232363⟩,
⟨128,648592114,648592498⟩]
theorem checked20001 : checkPrefixCuts (2^48) 2625503233 9 Manual.Count131072.C020001.packed 128 cuts20001 = true := by
 decide +kernel
def pointBounds20001 : List (Nat × Nat × Nat) := [(2625550336,100021757122413,100022137492681),(2625633280,100022164927780,100022545298293)]
theorem point_links_checked20001 : (cuts20001.take 2).map (fun c => (2625503233-1+2*2^9*c.k,100021521695798+c.lower,100021902065930+c.upper)) = pointBounds20001 := by
 decide +kernel
def cuts20002 : List PrefixCut := [⟨80,403182770,403183010⟩,
⟨128,651561176,651561565⟩]
theorem checked20002 : checkPrefixCuts (2^48) 2625634305 9 Manual.Count131072.C020002.packed 128 cuts20002 = true := by
 decide +kernel
def pointBounds20002 : List (Nat × Nat × Nat) := [(2625716224,100022573470682,100022953841438)]
theorem point_links_checked20002 : (cuts20002.take 1).map (fun c => (2625634305-1+2*2^9*c.k,100022170287912+c.lower,100022550658428+c.upper)) = pointBounds20002 := by
 decide +kernel
def cuts20003 : List PrefixCut := [⟨33,165404320,165404417⟩,
⟨114,580138735,580139072⟩,
⟨128,650242443,650242823⟩]
theorem checked20003 : checkPrefixCuts (2^48) 2625765377 9 Manual.Count131072.C020003.packed 128 cuts20003 = true := by
 decide +kernel
def pointBounds20003 : List (Nat × Nat × Nat) := [(2625799168,100022987253408,100023367624410),(2625882112,100023401987823,100023782359065)]
theorem point_links_checked20003 : (cuts20003.take 2).map (fun c => (2625765377-1+2*2^9*c.k,100022821849088+c.lower,100023202219993+c.upper)) = pointBounds20003 := by
 decide +kernel
def cuts20004 : List PrefixCut := [⟨67,332612168,332612364⟩,
⟨128,644957511,644957890⟩]
theorem checked20004 : checkPrefixCuts (2^48) 2625896449 9 Manual.Count131072.C020004.packed 128 cuts20004 = true := by
 decide +kernel
def pointBounds20004 : List (Nat × Nat × Nat) := [(2625965056,100023804703699,100024185075180)]
theorem point_links_checked20004 : (cuts20004.take 1).map (fun c => (2625896449-1+2*2^9*c.k,100023472091531+c.lower,100023852462816+c.upper)) = pointBounds20004 := by
 decide +kernel
def cuts20005 : List PrefixCut := [⟨20,99897497,99897559⟩,
⟨101,503016669,503016971⟩,
⟨128,638601646,638602026⟩]
theorem checked20005 : checkPrefixCuts (2^48) 2626027521 9 Manual.Count131072.C020005.packed 128 cuts20005 = true := by
 decide +kernel
def pointBounds20005 : List (Nat × Nat × Nat) := [(2626048000,100024216946539,100024597318265),(2626130944,100024620065711,100025000437677)]
theorem point_links_checked20005 : (cuts20005.take 2).map (fun c => (2626027521-1+2*2^9*c.k,100024117049042+c.lower,100024497420706+c.upper)) = pointBounds20005 := by
 decide +kernel
def cuts20006 : List PrefixCut := [⟨54,268700528,268700690⟩,
⟨128,642856890,642857271⟩]
theorem checked20006 : checkPrefixCuts (2^48) 2626158593 9 Manual.Count131072.C020006.packed 128 cuts20006 = true := by
 decide +kernel
def pointBounds20006 : List (Nat × Nat × Nat) := [(2626213888,100025024351216,100025404723422)]
theorem point_links_checked20006 : (cuts20006.take 1).map (fun c => (2626158593-1+2*2^9*c.k,100024755650688+c.lower,100025136022732+c.upper)) = pointBounds20006 := by
 decide +kernel
def cuts20007 : List PrefixCut := [⟨7,34617761,34617780⟩,
⟨88,437698736,437698993⟩,
⟨128,642717539,642717912⟩]
theorem checked20007 : checkPrefixCuts (2^48) 2626289665 9 Manual.Count131072.C020007.packed 128 cuts20007 = true := by
 decide +kernel
def pointBounds20007 : List (Nat × Nat × Nat) := [(2626296832,100025433125339,100025813497783),(2626379776,100025836206314,100026216578996)]
theorem point_links_checked20007 : (cuts20007.take 2).map (fun c => (2626289665-1+2*2^9*c.k,100025398507578+c.lower,100025778880003+c.upper)) = pointBounds20007 := by
 decide +kernel
def cuts20008 : List PrefixCut := [⟨41,211017096,211017221⟩,
⟨122,619109509,619109877⟩,
⟨128,650723275,650723662⟩]
theorem checked20008 : checkPrefixCuts (2^48) 2626420737 9 Manual.Count131072.C020008.packed 128 cuts20008 = true := by
 decide +kernel
def pointBounds20008 : List (Nat × Nat × Nat) := [(2626462720,100026252242213,100026632615136),(2626545664,100026660334626,100027040707792)]
theorem point_links_checked20008 : (cuts20008.take 2).map (fun c => (2626420737-1+2*2^9*c.k,100026041225117+c.lower,100026421597915+c.upper)) = pointBounds20008 := by
 decide +kernel
def cuts20009 : List PrefixCut := [⟨75,377966073,377966294⟩,
⟨128,645868435,645868811⟩]
theorem checked20009 : checkPrefixCuts (2^48) 2626551809 9 Manual.Count131072.C020009.packed 128 cuts20009 = true := by
 decide +kernel
def pointBounds20009 : List (Nat × Nat × Nat) := [(2626628608,100027069914465,100027450287871)]
theorem point_links_checked20009 : (cuts20009.take 1).map (fun c => (2626551809-1+2*2^9*c.k,100026691948392+c.lower,100027072321577+c.upper)) = pointBounds20009 := by
 decide +kernel
def cuts20010 : List PrefixCut := [⟨28,147451142,147451228⟩,
⟨109,558719622,558719946⟩,
⟨128,655051864,655052246⟩]
theorem checked20010 : checkPrefixCuts (2^48) 2626682881 9 Manual.Count131072.C020010.packed 128 cuts20010 = true := by
 decide +kernel
def pointBounds20010 : List (Nat × Nat × Nat) := [(2626711552,100027485267969,100027865641616),(2626794496,100027896536449,100028276910334)]
theorem point_links_checked20010 : (cuts20010.take 2).map (fun c => (2626682881-1+2*2^9*c.k,100027337816827+c.lower,100027718190388+c.upper)) = pointBounds20010 := by
 decide +kernel
def cuts20011 : List PrefixCut := [⟨62,312994492,312994679⟩,
⟨128,646339730,646340117⟩]
theorem checked20011 : checkPrefixCuts (2^48) 2626813953 9 Manual.Count131072.C020011.packed 128 cuts20011 = true := by
 decide +kernel
def pointBounds20011 : List (Nat × Nat × Nat) := [(2626877440,100028305863183,100028686237313)]
theorem point_links_checked20011 : (cuts20011.take 1).map (fun c => (2626813953-1+2*2^9*c.k,100027992868691+c.lower,100028373242634+c.upper)) = pointBounds20011 := by
 decide +kernel
def cuts20012 : List PrefixCut := [⟨15,74682731,74682775⟩,
⟨96,493091070,493091354⟩,
⟨128,654236335,654236714⟩]
theorem checked20012 : checkPrefixCuts (2^48) 2626945025 9 Manual.Count131072.C020012.packed 128 cuts20012 = true := by
 decide +kernel
def pointBounds20012 : List (Nat × Nat × Nat) := [(2626960384,100028713891152,100029094265526),(2627043328,100029132299491,100029512674105)]
theorem point_links_checked20012 : (cuts20012.take 2).map (fun c => (2626945025-1+2*2^9*c.k,100028639208421+c.lower,100029019582751+c.upper)) = pointBounds20012 := by
 decide +kernel
def cuts20013 : List PrefixCut := [⟨49,247392653,247392800⟩,
⟨128,645632349,645632730⟩]
theorem checked20013 : checkPrefixCuts (2^48) 2627076097 9 Manual.Count131072.C020013.packed 128 cuts20013 = true := by
 decide +kernel
def pointBounds20013 : List (Nat × Nat × Nat) := [(2627126272,100029540837409,100029921212265)]
theorem point_links_checked20013 : (cuts20013.take 1).map (fun c => (2627076097-1+2*2^9*c.k,100029293444756+c.lower,100029673819465+c.upper)) = pointBounds20013 := by
 decide +kernel
def cuts20014 : List PrefixCut := [⟨2,9321041,9321047⟩,
⟨83,425975621,425975869⟩,
⟨128,652564156,652564534⟩]
theorem checked20014 : checkPrefixCuts (2^48) 2627207169 9 Manual.Count131072.C020014.packed 128 cuts20014 = true := by
 decide +kernel
def pointBounds20014 : List (Nat × Nat × Nat) := [(2627209216,100029948398146,100030328773242),(2627292160,100030365052726,100030745428064)]
theorem point_links_checked20014 : (cuts20014.take 2).map (fun c => (2627207169-1+2*2^9*c.k,100029939077105+c.lower,100030319452195+c.upper)) = pointBounds20014 := by
 decide +kernel
def cuts20015 : List PrefixCut := [⟨36,178803880,178803984⟩,
⟨117,590718317,590718658⟩,
⟨128,648138916,648139290⟩]
theorem checked20015 : checkPrefixCuts (2^48) 2627338241 9 Manual.Count131072.C020015.packed 128 cuts20015 = true := by
 decide +kernel
def pointBounds20015 : List (Nat × Nat × Nat) := [(2627375104,100030770445141,100031150820713),(2627458048,100031182359578,100031562735387)]
theorem point_links_checked20015 : (cuts20015.take 2).map (fun c => (2627338241-1+2*2^9*c.k,100030591641261+c.lower,100030972016729+c.upper)) = pointBounds20015 := by
 decide +kernel
def cuts20016 : List PrefixCut := [⟨70,358551608,358551821⟩,
⟨128,652927304,652927691⟩]
theorem checked20016 : checkPrefixCuts (2^48) 2627469313 9 Manual.Count131072.C020016.packed 128 cuts20016 = true := by
 decide +kernel
def pointBounds20016 : List (Nat × Nat × Nat) := [(2627540992,100031598331785,100031978707840)]
theorem point_links_checked20016 : (cuts20016.take 1).map (fun c => (2627469313-1+2*2^9*c.k,100031239780177+c.lower,100031620156019+c.upper)) = pointBounds20016 := by
 decide +kernel
def cuts20017 : List PrefixCut := [⟨23,111299688,111299756⟩,
⟨104,519533147,519533457⟩,
⟨128,636934004,636934385⟩]
theorem checked20017 : checkPrefixCuts (2^48) 2627600385 9 Manual.Count131072.C020017.packed 128 cuts20017 = true := by
 decide +kernel
def pointBounds20017 : List (Nat × Nat × Nat) := [(2627623936,100032004007169,100032384383466),(2627706880,100032412240628,100032792617167)]
theorem point_links_checked20017 : (cuts20017.take 2).map (fun c => (2627600385-1+2*2^9*c.k,100031892707481+c.lower,100032273083710+c.upper)) = pointBounds20017 := by
 decide +kernel
def cuts20018 : List PrefixCut := [⟨57,289855608,289855776⟩,
⟨128,642472323,642472700⟩]
theorem checked20018 : checkPrefixCuts (2^48) 2627731457 9 Manual.Count131072.C020018.packed 128 cuts20018 = true := by
 decide +kernel
def pointBounds20018 : List (Nat × Nat × Nat) := [(2627789824,100032819497093,100033199873871)]
theorem point_links_checked20018 : (cuts20018.take 1).map (fun c => (2627731457-1+2*2^9*c.k,100032529641485+c.lower,100032910018095+c.upper)) = pointBounds20018 := by
 decide +kernel
def cuts20019 : List PrefixCut := [⟨10,50449525,50449554⟩,
⟨91,462714447,462714718⟩,
⟨128,654114942,654115325⟩]
theorem checked20019 : checkPrefixCuts (2^48) 2627862529 9 Manual.Count131072.C020019.packed 128 cuts20019 = true := by
 decide +kernel
def pointBounds20019 : List (Nat × Nat × Nat) := [(2627872768,100033222563333,100033602940349),(2627955712,100033634828255,100034015205513)]
theorem point_links_checked20019 : (cuts20019.take 2).map (fun c => (2627862529-1+2*2^9*c.k,100033172113808+c.lower,100033552490795+c.upper)) = pointBounds20019 := by
 decide +kernel
def cuts20020 : List PrefixCut := [⟨44,226742252,226742383⟩,
⟨125,635339659,635340029⟩,
⟨128,651297724,651298103⟩]
theorem checked20020 : checkPrefixCuts (2^48) 2627993601 9 Manual.Count131072.C020020.packed 128 cuts20020 = true := by
 decide +kernel
def pointBounds20020 : List (Nat × Nat × Nat) := [(2628038656,100034052971002,100034433348503),(2628121600,100034461568409,100034841946149)]
theorem point_links_checked20020 : (cuts20020.take 2).map (fun c => (2627993601-1+2*2^9*c.k,100033826228750+c.lower,100034206606120+c.upper)) = pointBounds20020 := by
 decide +kernel
def cuts20021 : List PrefixCut := [⟨78,391555430,391555660⟩,
⟨128,644732146,644732527⟩]
theorem checked20021 : checkPrefixCuts (2^48) 2628124673 9 Manual.Count131072.C020021.packed 128 cuts20021 = true := by
 decide +kernel
def pointBounds20021 : List (Nat × Nat × Nat) := [(2628204544,100034869081904,100035249459883)]
theorem point_links_checked20021 : (cuts20021.take 1).map (fun c => (2628124673-1+2*2^9*c.k,100034477526474+c.lower,100034857904223+c.upper)) = pointBounds20021 := by
 decide +kernel
def cuts20022 : List PrefixCut := [⟨31,157858107,157858202⟩,
⟨112,565881324,565881657⟩,
⟨128,647163158,647163538⟩]
theorem checked20022 : checkPrefixCuts (2^48) 2628255745 9 Manual.Count131072.C020022.packed 128 cuts20022 = true := by
 decide +kernel
def pointBounds20022 : List (Nat × Nat × Nat) := [(2628287488,100035280116727,100035660494952),(2628370432,100035688139944,100036068518407)]
theorem point_links_checked20022 : (cuts20022.take 2).map (fun c => (2628255745-1+2*2^9*c.k,100035122258620+c.lower,100035502636750+c.upper)) = pointBounds20022 := by
 decide +kernel
def cuts20023 : List PrefixCut := [⟨65,322337919,322338112⟩,
⟨128,639634782,639635164⟩]
theorem checked20023 : checkPrefixCuts (2^48) 2628386817 9 Manual.Count131072.C020023.packed 128 cuts20023 = true := by
 decide +kernel
def pointBounds20023 : List (Nat × Nat × Nat) := [(2628453376,100036091759697,100036472138400)]
theorem point_links_checked20023 : (cuts20023.take 1).map (fun c => (2628386817-1+2*2^9*c.k,100035769421778+c.lower,100036149800288+c.upper)) = pointBounds20023 := by
 decide +kernel
def cuts20024 : List PrefixCut := [⟨18,89201511,89201564⟩,
⟨99,495044508,495044798⟩,
⟨128,641530349,641530722⟩]
theorem checked20024 : checkPrefixCuts (2^48) 2628517889 9 Manual.Count131072.C020024.packed 128 cuts20024 = true := by
 decide +kernel
def pointBounds20024 : List (Nat × Nat × Nat) := [(2628536320,100036498258071,100036878637016),(2628619264,100036904101068,100037284480250)]
theorem point_links_checked20024 : (cuts20024.take 2).map (fun c => (2628517889-1+2*2^9*c.k,100036409056560+c.lower,100036789435452+c.upper)) = pointBounds20024 := by
 decide +kernel
def cuts20025 : List PrefixCut := [⟨52,268124808,268124965⟩,
⟨128,650385852,650386235⟩]
theorem checked20025 : checkPrefixCuts (2^48) 2628648961 9 Manual.Count131072.C020025.packed 128 cuts20025 = true := by
 decide +kernel
def pointBounds20025 : List (Nat × Nat × Nat) := [(2628702208,100037318711717,100037699091139)]
theorem point_links_checked20025 : (cuts20025.take 1).map (fun c => (2628648961-1+2*2^9*c.k,100037050586909+c.lower,100037430966174+c.upper)) = pointBounds20025 := by
 decide +kernel
def cuts20026 : List PrefixCut := [⟨5,26126114,26126129⟩,
⟨86,441031849,441032109⟩,
⟨128,653137295,653137679⟩]
theorem checked20026 : checkPrefixCuts (2^48) 2628780033 9 Manual.Count131072.C020026.packed 128 cuts20026 = true := by
 decide +kernel
def pointBounds20026 : List (Nat × Nat × Nat) := [(2628785152,100037727098875,100038107478538),(2628868096,100038142004610,100038522384518)]
theorem point_links_checked20026 : (cuts20026.take 2).map (fun c => (2628780033-1+2*2^9*c.k,100037700972761+c.lower,100038081352409+c.upper)) = pointBounds20026 := by
 decide +kernel
def cuts20027 : List PrefixCut := [⟨39,200752843,200752958⟩,
⟨120,607602486,607602843⟩,
⟨128,645503084,645503462⟩]
theorem checked20027 : checkPrefixCuts (2^48) 2628911105 9 Manual.Count131072.C020027.packed 128 cuts20027 = true := by
 decide +kernel
def pointBounds20027 : List (Nat × Nat × Nat) := [(2628951040,100038554862899,100038935243046),(2629033984,100038961712542,100039342092931)]
theorem point_links_checked20027 : (cuts20027.take 2).map (fun c => (2628911105-1+2*2^9*c.k,100038354110056+c.lower,100038734490088+c.upper)) = pointBounds20027 := by
 decide +kernel
def cuts20028 : List PrefixCut := [⟨73,365938411,365938628⟩,
⟨128,636798911,636799288⟩]
theorem checked20028 : checkPrefixCuts (2^48) 2629042177 9 Manual.Count131072.C020028.packed 128 cuts20028 = true := by
 decide +kernel
def pointBounds20028 : List (Nat × Nat × Nat) := [(2629116928,100039365551551,100039745932178)]
theorem point_links_checked20028 : (cuts20028.take 1).map (fun c => (2629042177-1+2*2^9*c.k,100038999613140+c.lower,100039379993550+c.upper)) = pointBounds20028 := by
 decide +kernel
def cuts20029 : List PrefixCut := [⟨26,128469333,128469409⟩,
⟨107,541596706,541597025⟩,
⟨128,648650135,648650515⟩]
theorem checked20029 : checkPrefixCuts (2^48) 2629173249 9 Manual.Count131072.C020029.packed 128 cuts20029 = true := by
 decide +kernel
def pointBounds20029 : List (Nat × Nat × Nat) := [(2629199872,100039764881384,100040145262247),(2629282816,100040178008757,100040558389863)]
theorem point_links_checked20029 : (cuts20029.take 2).map (fun c => (2629173249-1+2*2^9*c.k,100039636412051+c.lower,100040016792838+c.upper)) = pointBounds20029 := by
 decide +kernel
def cuts20030 : List PrefixCut := [⟨60,301350607,301350783⟩,
⟨128,639732694,639733063⟩]
theorem checked20030 : checkPrefixCuts (2^48) 2629304321 9 Manual.Count131072.C020030.packed 128 cuts20030 = true := by
 decide +kernel
def pointBounds20030 : List (Nat × Nat × Nat) := [(2629365760,100040586412793,100040966794136)]
theorem point_links_checked20030 : (cuts20030.take 1).map (fun c => (2629304321-1+2*2^9*c.k,100040285062186+c.lower,100040665443353+c.upper)) = pointBounds20030 := by
 decide +kernel
def cuts20031 : List PrefixCut := [⟨13,64335479,64335518⟩,
⟨94,470572922,470573200⟩,
⟨128,645909422,645909802⟩]
theorem checked20031 : checkPrefixCuts (2^48) 2629435393 9 Manual.Count131072.C020031.packed 128 cuts20031 = true := by
 decide +kernel
def pointBounds20031 : List (Nat × Nat × Nat) := [(2629448704,100040989130359,100041369511934),(2629531648,100041395367802,100041775749616)]
theorem point_links_checked20031 : (cuts20031.take 2).map (fun c => (2629435393-1+2*2^9*c.k,100040924794880+c.lower,100041305176416+c.upper)) = pointBounds20031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000000
