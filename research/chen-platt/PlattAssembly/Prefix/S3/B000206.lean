import PlattAssemblyKernel
import PlattCertificates.Count131072.C026592
import PlattCertificates.Count131072.C026593
import PlattCertificates.Count131072.C026594
import PlattCertificates.Count131072.C026595
import PlattCertificates.Count131072.C026596
import PlattCertificates.Count131072.C026597
import PlattCertificates.Count131072.C026598
import PlattCertificates.Count131072.C026599
import PlattCertificates.Count131072.C026600
import PlattCertificates.Count131072.C026601
import PlattCertificates.Count131072.C026602
import PlattCertificates.Count131072.C026603
import PlattCertificates.Count131072.C026604
import PlattCertificates.Count131072.C026605
import PlattCertificates.Count131072.C026606
import PlattCertificates.Count131072.C026607
import PlattCertificates.Count131072.C026608
import PlattCertificates.Count131072.C026609
import PlattCertificates.Count131072.C026610
import PlattCertificates.Count131072.C026611
import PlattCertificates.Count131072.C026612
import PlattCertificates.Count131072.C026613
import PlattCertificates.Count131072.C026614
import PlattCertificates.Count131072.C026615
import PlattCertificates.Count131072.C026616
import PlattCertificates.Count131072.C026617
import PlattCertificates.Count131072.C026618
import PlattCertificates.Count131072.C026619
import PlattCertificates.Count131072.C026620
import PlattCertificates.Count131072.C026621
import PlattCertificates.Count131072.C026622
import PlattCertificates.Count131072.C026623
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000206
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26592 : List PrefixCut := [⟨6,22102389,22102401⟩,
⟨113,419858190,419858419⟩,
⟨128,474789605,474789864⟩]
theorem checked26592 : checkPrefixCuts (2^48) 3489398785 9 Manual.Count131072.C026592.packed 128 cuts26592 = true := by
 decide +kernel
def pointBounds26592 : List (Nat × Nat × Nat) := [(3489404928,103689078031369,103689460490847),(3489514496,103689475787170,103689858246865)]
theorem point_links_checked26592 : (cuts26592.take 2).map (fun c => (3489398785-1+2*2^9*c.k,103689055928980+c.lower,103689438388446+c.upper)) = pointBounds26592 := by
 decide +kernel
def cuts26593 : List PrefixCut := [⟨92,346441655,346441849⟩,
⟨128,479288826,479289095⟩]
theorem checked26593 : checkPrefixCuts (2^48) 3489529857 9 Manual.Count131072.C026593.packed 128 cuts26593 = true := by
 decide +kernel
def pointBounds26593 : List (Nat × Nat × Nat) := [(3489624064,103689877160240,103690259620159)]
theorem point_links_checked26593 : (cuts26593.take 1).map (fun c => (3489529857-1+2*2^9*c.k,103689530718585+c.lower,103689913178310+c.upper)) = pointBounds26593 := by
 decide +kernel
def cuts26594 : List PrefixCut := [⟨71,266416089,266416240⟩,
⟨128,477334964,477335236⟩]
theorem checked26594 : checkPrefixCuts (2^48) 3489660929 9 Manual.Count131072.C026594.packed 128 cuts26594 = true := by
 decide +kernel
def pointBounds26594 : List (Nat × Nat × Nat) := [(3489733632,103690276423500,103690658883645)]
theorem point_links_checked26594 : (cuts26594.take 1).map (fun c => (3489660929-1+2*2^9*c.k,103690010007411+c.lower,103690392467405+c.upper)) = pointBounds26594 := by
 decide +kernel
def cuts26595 : List PrefixCut := [⟨50,185831557,185831663⟩,
⟨128,480301245,480301516⟩]
theorem checked26595 : checkPrefixCuts (2^48) 3489792001 9 Manual.Count131072.C026595.packed 128 cuts26595 = true := by
 decide +kernel
def pointBounds26595 : List (Nat × Nat × Nat) := [(3489843200,103690673173932,103691055634304)]
theorem point_links_checked26595 : (cuts26595.take 1).map (fun c => (3489792001-1+2*2^9*c.k,103690487342375+c.lower,103690869802641+c.upper)) = pointBounds26595 := by
 decide +kernel
def cuts26596 : List PrefixCut := [⟨29,109285177,109285238⟩,
⟨128,480121921,480122199⟩]
theorem checked26596 : checkPrefixCuts (2^48) 3489923073 9 Manual.Count131072.C026596.packed 128 cuts26596 = true := by
 decide +kernel
def pointBounds26596 : List (Nat × Nat × Nat) := [(3489952768,103691076928797,103691459389395)]
theorem point_links_checked26596 : (cuts26596.take 1).map (fun c => (3489923073-1+2*2^9*c.k,103690967643620+c.lower,103691350104157+c.upper)) = pointBounds26596 := by
 decide +kernel
def cuts26597 : List PrefixCut := [⟨8,29840679,29840696⟩,
⟨115,430102375,430102616⟩,
⟨128,480023304,480023573⟩]
theorem checked26597 : checkPrefixCuts (2^48) 3490054145 9 Manual.Count131072.C026597.packed 128 cuts26597 = true := by
 decide +kernel
def pointBounds26597 : List (Nat × Nat × Nat) := [(3490062336,103691477606220,103691860067052),(3490171904,103691877867916,103692260328972)]
theorem point_links_checked26597 : (cuts26597.take 2).map (fun c => (3490054145-1+2*2^9*c.k,103691447765541+c.lower,103691830226356+c.upper)) = pointBounds26597 := by
 decide +kernel
def cuts26598 : List PrefixCut := [⟨94,351053973,351054166⟩,
⟨128,478876185,478876454⟩]
theorem checked26598 : checkPrefixCuts (2^48) 3490185217 9 Manual.Count131072.C026598.packed 128 cuts26598 = true := by
 decide +kernel
def pointBounds26598 : List (Nat × Nat × Nat) := [(3490281472,103692278842818,103692661304095)]
theorem point_links_checked26598 : (cuts26598.take 1).map (fun c => (3490185217-1+2*2^9*c.k,103691927788845+c.lower,103692310249929+c.upper)) = pointBounds26598 := by
 decide +kernel
def cuts26599 : List PrefixCut := [⟨73,276204496,276204648⟩,
⟨128,482245167,482245435⟩]
theorem checked26599 : checkPrefixCuts (2^48) 3490316289 9 Manual.Count131072.C026599.packed 128 cuts26599 = true := by
 decide +kernel
def pointBounds26599 : List (Nat × Nat × Nat) := [(3490391040,103692682869526,103693065331031)]
theorem point_links_checked26599 : (cuts26599.take 1).map (fun c => (3490316289-1+2*2^9*c.k,103692406665030+c.lower,103692789126383+c.upper)) = pointBounds26599 := by
 decide +kernel
def cuts26600 : List PrefixCut := [⟨52,200231297,200231413⟩,
⟨128,479646683,479646958⟩]
theorem checked26600 : checkPrefixCuts (2^48) 3490447361 9 Manual.Count131072.C026600.packed 128 cuts26600 = true := by
 decide +kernel
def pointBounds26600 : List (Nat × Nat × Nat) := [(3490500608,103693089141494,103693471603231)]
theorem point_links_checked26600 : (cuts26600.take 1).map (fun c => (3490447361-1+2*2^9*c.k,103692888910197+c.lower,103693271371818+c.upper)) = pointBounds26600 := by
 decide +kernel
def cuts26601 : List PrefixCut := [⟨31,116844610,116844674⟩,
⟨128,482531548,482531818⟩]
theorem checked26601 : checkPrefixCuts (2^48) 3490578433 9 Manual.Count131072.C026601.packed 128 cuts26601 = true := by
 decide +kernel
def pointBounds26601 : List (Nat × Nat × Nat) := [(3490610176,103693485401490,103693867863450)]
theorem point_links_checked26601 : (cuts26601.take 1).map (fun c => (3490578433-1+2*2^9*c.k,103693368556880+c.lower,103693751018776+c.upper)) = pointBounds26601 := by
 decide +kernel
def cuts26602 : List PrefixCut := [⟨10,38382415,38382436⟩,
⟨117,443003510,443003761⟩,
⟨128,485013063,485013338⟩]
theorem checked26602 : checkPrefixCuts (2^48) 3490709505 9 Manual.Count131072.C026602.packed 128 cuts26602 = true := by
 decide +kernel
def pointBounds26602 : List (Nat × Nat × Nat) := [(3490719744,103693889470843,103694271933030),(3490829312,103694294091938,103694676554355)]
theorem point_links_checked26602 : (cuts26602.take 2).map (fun c => (3490709505-1+2*2^9*c.k,103693851088428+c.lower,103694233550594+c.upper)) = pointBounds26602 := by
 decide +kernel
def cuts26603 : List PrefixCut := [⟨96,357841638,357841839⟩,
⟨128,479915103,479915370⟩]
theorem checked26603 : checkPrefixCuts (2^48) 3490840577 9 Manual.Count131072.C026603.packed 128 cuts26603 = true := by
 decide +kernel
def pointBounds26603 : List (Nat × Nat × Nat) := [(3490938880,103694693943129,103695076405771)]
theorem point_links_checked26603 : (cuts26603.take 1).map (fun c => (3490840577-1+2*2^9*c.k,103694336101491+c.lower,103694718563932+c.upper)) = pointBounds26603 := by
 decide +kernel
def cuts26604 : List PrefixCut := [⟨75,277200775,277200933⟩,
⟨128,479735758,479736029⟩]
theorem checked26604 : checkPrefixCuts (2^48) 3490971649 9 Manual.Count131072.C026604.packed 128 cuts26604 = true := by
 decide +kernel
def pointBounds26604 : List (Nat × Nat × Nat) := [(3491048448,103695093217369,103695475680235)]
theorem point_links_checked26604 : (cuts26604.take 1).map (fun c => (3490971649-1+2*2^9*c.k,103694816016594+c.lower,103695198479302+c.upper)) = pointBounds26604 := by
 decide +kernel
def cuts26605 : List PrefixCut := [⟨54,203983063,203983179⟩,
⟨128,482378447,482378717⟩]
theorem checked26605 : checkPrefixCuts (2^48) 3491102721 9 Manual.Count131072.C026605.packed 128 cuts26605 = true := by
 decide +kernel
def pointBounds26605 : List (Nat × Nat × Nat) := [(3491158016,103695499735415,103695882198510)]
theorem point_links_checked26605 : (cuts26605.take 1).map (fun c => (3491102721-1+2*2^9*c.k,103695295752352+c.lower,103695678215331+c.upper)) = pointBounds26605 := by
 decide +kernel
def cuts26606 : List PrefixCut := [⟨33,124562437,124562506⟩,
⟨128,477039243,477039510⟩]
theorem checked26606 : checkPrefixCuts (2^48) 3491233793 9 Manual.Count131072.C026606.packed 128 cuts26606 = true := by
 decide +kernel
def pointBounds26606 : List (Nat × Nat × Nat) := [(3491267584,103695902693236,103696285156554)]
theorem point_links_checked26606 : (cuts26606.take 1).map (fun c => (3491233793-1+2*2^9*c.k,103695778130799+c.lower,103696160594048+c.upper)) = pointBounds26606 := by
 decide +kernel
def cuts26607 : List PrefixCut := [⟨12,46034111,46034135⟩,
⟨119,451062726,451062973⟩,
⟨128,485808817,485809085⟩]
theorem checked26607 : checkPrefixCuts (2^48) 3491364865 9 Manual.Count131072.C026607.packed 128 cuts26607 = true := by
 decide +kernel
def pointBounds26607 : List (Nat × Nat × Nat) := [(3491377152,103696301204153,103696683667693),(3491486720,103696706232768,103697088696531)]
theorem point_links_checked26607 : (cuts26607.take 2).map (fun c => (3491364865-1+2*2^9*c.k,103696255170042+c.lower,103696637633558+c.upper)) = pointBounds26607 := by
 decide +kernel
def cuts26608 : List PrefixCut := [⟨98,366964612,366964820⟩,
⟨128,479341378,479341648⟩]
theorem checked26608 : checkPrefixCuts (2^48) 3491495937 9 Manual.Count131072.C026608.packed 128 cuts26608 = true := by
 decide +kernel
def pointBounds26608 : List (Nat × Nat × Nat) := [(3491596288,103697107943471,103697490407463)]
theorem point_links_checked26608 : (cuts26608.take 1).map (fun c => (3491495937-1+2*2^9*c.k,103696740978859+c.lower,103697123442643+c.upper)) = pointBounds26608 := by
 decide +kernel
def cuts26609 : List PrefixCut := [⟨77,288273286,288273445⟩,
⟨128,482547787,482548051⟩]
theorem checked26609 : checkPrefixCuts (2^48) 3491627009 9 Manual.Count131072.C026609.packed 128 cuts26609 = true := by
 decide +kernel
def pointBounds26609 : List (Nat × Nat × Nat) := [(3491705856,103697508593523,103697891057736)]
theorem point_links_checked26609 : (cuts26609.take 1).map (fun c => (3491627009-1+2*2^9*c.k,103697220320237+c.lower,103697602784291+c.upper)) = pointBounds26609 := by
 decide +kernel
def cuts26610 : List PrefixCut := [⟨56,211844575,211844693⟩,
⟨128,488091807,488092075⟩]
theorem checked26610 : checkPrefixCuts (2^48) 3491758081 9 Manual.Count131072.C026610.packed 128 cuts26610 = true := by
 decide +kernel
def pointBounds26610 : List (Nat × Nat × Nat) := [(3491815424,103697914712599,103698297177035)]
theorem point_links_checked26610 : (cuts26610.take 1).map (fun c => (3491758081-1+2*2^9*c.k,103697702868024+c.lower,103698085332342+c.upper)) = pointBounds26610 := by
 decide +kernel
def cuts26611 : List PrefixCut := [⟨35,130665239,130665311⟩,
⟨128,474209157,474209422⟩]
theorem checked26611 : checkPrefixCuts (2^48) 3491889153 9 Manual.Count131072.C026611.packed 128 cuts26611 = true := by
 decide +kernel
def pointBounds26611 : List (Nat × Nat × Nat) := [(3491924992,103698321625070,103698704089728)]
theorem point_links_checked26611 : (cuts26611.take 1).map (fun c => (3491889153-1+2*2^9*c.k,103698190959831+c.lower,103698573424417+c.upper)) = pointBounds26611 := by
 decide +kernel
def cuts26612 : List PrefixCut := [⟨14,54005359,54005389⟩,
⟨121,455894741,455894998⟩,
⟨128,479994808,479995079⟩]
theorem checked26612 : checkPrefixCuts (2^48) 3492020225 9 Manual.Count131072.C026612.packed 128 cuts26612 = true := by
 decide +kernel
def pointBounds26612 : List (Nat × Nat × Nat) := [(3492034560,103698719174347,103699101639228),(3492144128,103699121063729,103699503528837)]
theorem point_links_checked26612 : (cuts26612.take 2).map (fun c => (3492020225-1+2*2^9*c.k,103698665168988+c.lower,103699047633839+c.upper)) = pointBounds26612 := by
 decide +kernel
def cuts26613 : List PrefixCut := [⟨100,375116918,375117125⟩,
⟨128,480621596,480621863⟩]
theorem checked26613 : checkPrefixCuts (2^48) 3492151297 9 Manual.Count131072.C026613.packed 128 cuts26613 = true := by
 decide +kernel
def pointBounds26613 : List (Nat × Nat × Nat) := [(3492253696,103699520280714,103699902746043)]
theorem point_links_checked26613 : (cuts26613.take 1).map (fun c => (3492151297-1+2*2^9*c.k,103699145163796+c.lower,103699527628918+c.upper)) = pointBounds26613 := by
 decide +kernel
def cuts26614 : List PrefixCut := [⟨79,300953650,300953818⟩,
⟨128,479233521,479233792⟩]
theorem checked26614 : checkPrefixCuts (2^48) 3492282369 9 Manual.Count131072.C026614.packed 128 cuts26614 = true := by
 decide +kernel
def pointBounds26614 : List (Nat × Nat × Nat) := [(3492363264,103699926739042,103700309204599)]
theorem point_links_checked26614 : (cuts26614.take 1).map (fun c => (3492282369-1+2*2^9*c.k,103699625785392+c.lower,103700008250781+c.upper)) = pointBounds26614 := by
 decide +kernel
def cuts26615 : List PrefixCut := [⟨58,220186682,220186804⟩,
⟨128,481875055,481875324⟩]
theorem checked26615 : checkPrefixCuts (2^48) 3492413441 9 Manual.Count131072.C026615.packed 128 cuts26615 = true := by
 decide +kernel
def pointBounds26615 : List (Nat × Nat × Nat) := [(3492472832,103700325205595,103700707671377)]
theorem point_links_checked26615 : (cuts26615.take 1).map (fun c => (3492413441-1+2*2^9*c.k,103700105018913+c.lower,103700487484573+c.upper)) = pointBounds26615 := by
 decide +kernel
def cuts26616 : List PrefixCut := [⟨37,140795340,140795418⟩,
⟨128,478311022,478311289⟩]
theorem checked26616 : checkPrefixCuts (2^48) 3492544513 9 Manual.Count131072.C026616.packed 128 cuts26616 = true := by
 decide +kernel
def pointBounds26616 : List (Nat × Nat × Nat) := [(3492582400,103700727689308,103701110155315)]
theorem point_links_checked26616 : (cuts26616.take 1).map (fun c => (3492544513-1+2*2^9*c.k,103700586893968+c.lower,103700969359897+c.upper)) = pointBounds26616 := by
 decide +kernel
def cuts26617 : List PrefixCut := [⟨16,60764753,60764787⟩,
⟨123,463062103,463062363⟩,
⟨128,482564177,482564448⟩]
theorem checked26617 : checkPrefixCuts (2^48) 3492675585 9 Manual.Count131072.C026617.packed 128 cuts26617 = true := by
 decide +kernel
def pointBounds26617 : List (Nat × Nat × Nat) := [(3492691968,103701125969743,103701508435973),(3492801536,103701528267093,103701910733549)]
theorem point_links_checked26617 : (cuts26617.take 2).map (fun c => (3492675585-1+2*2^9*c.k,103701065204990+c.lower,103701447671186+c.upper)) = pointBounds26617 := by
 decide +kernel
def cuts26618 : List PrefixCut := [⟨102,376335738,376335955⟩,
⟨128,472714583,472714853⟩]
theorem checked26618 : checkPrefixCuts (2^48) 3492806657 9 Manual.Count131072.C026618.packed 128 cuts26618 = true := by
 decide +kernel
def pointBounds26618 : List (Nat × Nat × Nat) := [(3492911104,103701924104905,103702306571589)]
theorem point_links_checked26618 : (cuts26618.take 1).map (fun c => (3492806657-1+2*2^9*c.k,103701547769167+c.lower,103701930235634+c.upper)) = pointBounds26618 := by
 decide +kernel
def cuts26619 : List PrefixCut := [⟨81,302589324,302589492⟩,
⟨128,478418229,478418497⟩]
theorem checked26619 : checkPrefixCuts (2^48) 3492937729 9 Manual.Count131072.C026619.packed 128 cuts26619 = true := by
 decide +kernel
def pointBounds26619 : List (Nat × Nat × Nat) := [(3493020672,103702323073074,103702705539979)]
theorem point_links_checked26619 : (cuts26619.take 1).map (fun c => (3492937729-1+2*2^9*c.k,103702020483750+c.lower,103702402950487+c.upper)) = pointBounds26619 := by
 decide +kernel
def cuts26620 : List PrefixCut := [⟨60,226027674,226027800⟩,
⟨128,484363202,484363472⟩]
theorem checked26620 : checkPrefixCuts (2^48) 3493068801 9 Manual.Count131072.C026620.packed 128 cuts26620 = true := by
 decide +kernel
def pointBounds26620 : List (Nat × Nat × Nat) := [(3493130240,103702724929653,103703107396784)]
theorem point_links_checked26620 : (cuts26620.take 1).map (fun c => (3493068801-1+2*2^9*c.k,103702498901979+c.lower,103702881368984+c.upper)) = pointBounds26620 := by
 decide +kernel
def cuts26621 : List PrefixCut := [⟨39,144233714,144233791⟩,
⟨128,476367880,476368143⟩]
theorem checked26621 : checkPrefixCuts (2^48) 3493199873 9 Manual.Count131072.C026621.packed 128 cuts26621 = true := by
 decide +kernel
def pointBounds26621 : List (Nat × Nat × Nat) := [(3493239808,103703127498895,103703509966247)]
theorem point_links_checked26621 : (cuts26621.take 1).map (fun c => (3493199873-1+2*2^9*c.k,103702983265181+c.lower,103703365732456+c.upper)) = pointBounds26621 := by
 decide +kernel
def cuts26622 : List PrefixCut := [⟨18,68569085,68569123⟩,
⟨125,466681473,466681733⟩,
⟨128,477800401,477800668⟩]
theorem checked26622 : checkPrefixCuts (2^48) 3493330945 9 Manual.Count131072.C026622.packed 128 cuts26622 = true := by
 decide +kernel
def pointBounds26622 : List (Nat × Nat × Nat) := [(3493349376,103703528202146,103703910669722),(3493458944,103703926314534,103704308782332)]
theorem point_links_checked26622 : (cuts26622.take 2).map (fun c => (3493330945-1+2*2^9*c.k,103703459633061+c.lower,103703842100599+c.upper)) = pointBounds26622 := by
 decide +kernel
def cuts26623 : List PrefixCut := [⟨104,384161018,384161237⟩,
⟨128,475445887,475446154⟩]
theorem checked26623 : checkPrefixCuts (2^48) 3493462017 9 Manual.Count131072.C026623.packed 128 cuts26623 = true := by
 decide +kernel
def pointBounds26623 : List (Nat × Nat × Nat) := [(3493568512,103704321594480,103704704062504)]
theorem point_links_checked26623 : (cuts26623.take 1).map (fun c => (3493462017-1+2*2^9*c.k,103703937433462+c.lower,103704319901267+c.upper)) = pointBounds26623 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000206
