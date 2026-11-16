import PlattAssemblyKernel
import PlattCertificates.Count131072.C013648
import PlattCertificates.Count131072.C013649
import PlattCertificates.Count131072.C013650
import PlattCertificates.Count131072.C013651
import PlattCertificates.Count131072.C013652
import PlattCertificates.Count131072.C013653
import PlattCertificates.Count131072.C013654
import PlattCertificates.Count131072.C013655
import PlattCertificates.Count131072.C013656
import PlattCertificates.Count131072.C013657
import PlattCertificates.Count131072.C013658
import PlattCertificates.Count131072.C013659
import PlattCertificates.Count131072.C013660
import PlattCertificates.Count131072.C013661
import PlattCertificates.Count131072.C013662
import PlattCertificates.Count131072.C013663
import PlattCertificates.Count131072.C013664
import PlattCertificates.Count131072.C013665
import PlattCertificates.Count131072.C013666
import PlattCertificates.Count131072.C013667
import PlattCertificates.Count131072.C013668
import PlattCertificates.Count131072.C013669
import PlattCertificates.Count131072.C013670
import PlattCertificates.Count131072.C013671
import PlattCertificates.Count131072.C013672
import PlattCertificates.Count131072.C013673
import PlattCertificates.Count131072.C013674
import PlattCertificates.Count131072.C013675
import PlattCertificates.Count131072.C013676
import PlattCertificates.Count131072.C013677
import PlattCertificates.Count131072.C013678
import PlattCertificates.Count131072.C013679
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13648 : List PrefixCut := [⟨11,83054165,83054226⟩,
⟨66,502242107,502242459⟩,
⟨121,917963029,917963680⟩,
⟨128,972596080,972596769⟩]
theorem checked13648 : checkPrefixCuts (2^48) 1792802817 9 Manual.Count131072.C013648.packed 128 cuts13648 = true := by
 decide +kernel
def pointBounds13648 : List (Nat × Nat × Nat) := [(1792814080,95026508532526,95026885716288),(1792870400,95026927720468,95027304904521),(1792926720,95027343441390,95027720625742)]
theorem point_links_checked13648 : (cuts13648.take 3).map (fun c => (1792802817-1+2*2^9*c.k,95026425478361+c.lower,95026802662062+c.upper)) = pointBounds13648 := by
 decide +kernel
def cuts13649 : List PrefixCut := [⟨48,367668385,367668645⟩,
⟨103,782578272,782578824⟩,
⟨128,975193837,975194526⟩]
theorem checked13649 : checkPrefixCuts (2^48) 1792933889 9 Manual.Count131072.C013649.packed 128 cuts13649 = true := by
 decide +kernel
def pointBounds13649 : List (Nat × Nat × Nat) := [(1792983040,95027765742826,95028142927476),(1793039360,95028180652713,95028557837655)]
theorem point_links_checked13649 : (cuts13649.take 2).map (fun c => (1792933889-1+2*2^9*c.k,95027398074441+c.lower,95027775258831+c.upper)) = pointBounds13649 := by
 decide +kernel
def cuts13650 : List PrefixCut := [⟨30,220554651,220554804⟩,
⟨85,634339628,634340068⟩,
⟨128,958169144,958169812⟩]
theorem checked13650 : checkPrefixCuts (2^48) 1793064961 9 Manual.Count131072.C013650.packed 128 cuts13650 = true := by
 decide +kernel
def pointBounds13650 : List (Nat × Nat × Nat) := [(1793095680,95028593822929,95028971008161),(1793152000,95029007607906,95029384793425)]
theorem point_links_checked13650 : (cuts13650.take 2).map (fun c => (1793064961-1+2*2^9*c.k,95028373268278+c.lower,95028750453357+c.upper)) = pointBounds13650 := by
 decide +kernel
def cuts13651 : List PrefixCut := [⟨12,85547413,85547474⟩,
⟨67,506840687,506841050⟩,
⟨122,920272750,920273403⟩,
⟨128,965005513,965006199⟩]
theorem checked13651 : checkPrefixCuts (2^48) 1793196033 9 Manual.Count131072.C013651.packed 128 cuts13651 = true := by
 decide +kernel
def pointBounds13651 : List (Nat × Nat × Nat) := [(1793208320,95029416984835,95029794170643),(1793264640,95029838278109,95030215464219),(1793320960,95030251710172,95030628896572)]
theorem point_links_checked13651 : (cuts13651.take 3).map (fun c => (1793196033-1+2*2^9*c.k,95029331437422+c.lower,95029708623169+c.upper)) = pointBounds13651 := by
 decide +kernel
def cuts13652 : List PrefixCut := [⟨49,373395000,373395263⟩,
⟨104,797944649,797945206⟩,
⟨128,980159405,980160091⟩]
theorem checked13652 : checkPrefixCuts (2^48) 1793327105 9 Manual.Count131072.C013652.packed 128 cuts13652 = true := by
 decide +kernel
def pointBounds13652 : List (Nat × Nat × Nat) := [(1793377280,95030669837935,95031047024631),(1793433600,95031094387584,95031471574574)]
theorem point_links_checked13652 : (cuts13652.take 2).map (fun c => (1793327105-1+2*2^9*c.k,95030296442935+c.lower,95030673629368+c.upper)) = pointBounds13652 := by
 decide +kernel
def cuts13653 : List PrefixCut := [⟨31,231335355,231335517⟩,
⟨86,639693495,639693942⟩,
⟨128,953565024,953565692⟩]
theorem checked13653 : checkPrefixCuts (2^48) 1793458177 9 Manual.Count131072.C013653.packed 128 cuts13653 = true := by
 decide +kernel
def pointBounds13653 : List (Nat × Nat × Nat) := [(1793489920,95031507937695,95031885124976),(1793546240,95031916295835,95032293483401)]
theorem point_links_checked13653 : (cuts13653.take 2).map (fun c => (1793458177-1+2*2^9*c.k,95031276602340+c.lower,95031653789459+c.upper)) = pointBounds13653 := by
 decide +kernel
def cuts13654 : List PrefixCut := [⟨13,92904500,92904567⟩,
⟨68,510809739,510810097⟩,
⟨123,928701816,928702464⟩,
⟨128,966677091,966677764⟩]
theorem checked13654 : checkPrefixCuts (2^48) 1793589249 9 Manual.Count131072.C013654.packed 128 cuts13654 = true := by
 decide +kernel
def pointBounds13654 : List (Nat × Nat × Nat) := [(1793602560,95032323071864,95032700259718),(1793658880,95032740977103,95033118165248),(1793715200,95033158869180,95033536057615)]
theorem point_links_checked13654 : (cuts13654.take 3).map (fun c => (1793589249-1+2*2^9*c.k,95032230167364+c.lower,95032607355151+c.upper)) = pointBounds13654 := by
 decide +kernel
def cuts13655 : List PrefixCut := [⟨50,378648326,378648597⟩,
⟨105,789609840,789610398⟩,
⟨128,964409750,964410434⟩]
theorem checked13655 : checkPrefixCuts (2^48) 1793720321 9 Manual.Count131072.C013655.packed 128 cuts13655 = true := by
 decide +kernel
def pointBounds13655 : List (Nat × Nat × Nat) := [(1793771520,95033575492781,95033952681512),(1793827840,95033986454295,95034363643313)]
theorem point_links_checked13655 : (cuts13655.take 2).map (fun c => (1793720321-1+2*2^9*c.k,95033196844455+c.lower,95033574032915+c.upper)) = pointBounds13655 := by
 decide +kernel
def cuts13656 : List PrefixCut := [⟨32,239914636,239914804⟩,
⟨87,656028256,656028719⟩,
⟨128,959475434,959476111⟩]
theorem checked13656 : checkPrefixCuts (2^48) 1793851393 9 Manual.Count131072.C013656.packed 128 cuts13656 = true := by
 decide +kernel
def pointBounds13656 : List (Nat × Nat × Nat) := [(1793884160,95034401168841,95034778358153),(1793940480,95034817282461,95035194472068)]
theorem point_links_checked13656 : (cuts13656.take 2).map (fun c => (1793851393-1+2*2^9*c.k,95034161254205+c.lower,95034538443349+c.upper)) = pointBounds13656 := by
 decide +kernel
def cuts13657 : List PrefixCut := [⟨14,106848102,106848177⟩,
⟨69,524975263,524975627⟩,
⟨124,938225658,938226315⟩,
⟨128,969289515,969290194⟩]
theorem checked13657 : checkPrefixCuts (2^48) 1793982465 9 Manual.Count131072.C013657.packed 128 cuts13657 = true := by
 decide +kernel
def pointBounds13657 : List (Nat × Nat × Nat) := [(1793996800,95035227577741,95035604767637),(1794053120,95035645704902,95036022895087),(1794109440,95036058955297,95036436145775)]
theorem point_links_checked13657 : (cuts13657.take 3).map (fun c => (1793982465-1+2*2^9*c.k,95035120729639+c.lower,95035497919460+c.upper)) = pointBounds13657 := by
 decide +kernel
def cuts13658 : List PrefixCut := [⟨51,380290950,380291221⟩,
⟨106,784573166,784573723⟩,
⟨128,954471528,954472205⟩]
theorem checked13658 : checkPrefixCuts (2^48) 1794113537 9 Manual.Count131072.C013658.packed 128 cuts13658 = true := by
 decide +kernel
def pointBounds13658 : List (Nat × Nat × Nat) := [(1794165760,95036470310104,95036847500875),(1794222080,95036874592320,95037251783377)]
theorem point_links_checked13658 : (cuts13658.take 2).map (fun c => (1794113537-1+2*2^9*c.k,95036090019154+c.lower,95036467209654+c.upper)) = pointBounds13658 := by
 decide +kernel
def cuts13659 : List PrefixCut := [⟨33,255235703,255235882⟩,
⟨88,665610579,665611044⟩,
⟨128,971971648,971972327⟩]
theorem checked13659 : checkPrefixCuts (2^48) 1794244609 9 Manual.Count131072.C013659.packed 128 cuts13659 = true := by
 decide +kernel
def pointBounds13659 : List (Nat × Nat × Nat) := [(1794278400,95037299726385,95037676917741),(1794334720,95037710101261,95038087292903)]
theorem point_links_checked13659 : (cuts13659.take 2).map (fun c => (1794244609-1+2*2^9*c.k,95037044490682+c.lower,95037421681859+c.upper)) = pointBounds13659 := by
 decide +kernel
def cuts13660 : List PrefixCut := [⟨15,110275677,110275752⟩,
⟨70,530036471,530036837⟩,
⟨125,942882442,942883105⟩,
⟨128,963900845,963901524⟩]
theorem checked13660 : checkPrefixCuts (2^48) 1794375681 9 Manual.Count131072.C013660.packed 128 cuts13660 = true := by
 decide +kernel
def pointBounds13660 : List (Nat × Nat × Nat) := [(1794391040,95038126738007,95038503929938),(1794447360,95038546498801,95038923691023),(1794503680,95038959344772,95039336537291)]
theorem point_links_checked13660 : (cuts13660.take 3).map (fun c => (1794375681-1+2*2^9*c.k,95038016462330+c.lower,95038393654186+c.upper)) = pointBounds13660 := by
 decide +kernel
def cuts13661 : List PrefixCut := [⟨52,388834423,388834696⟩,
⟨107,813574756,813575327⟩,
⟨128,968692586,968693264⟩]
theorem checked13661 : checkPrefixCuts (2^48) 1794506753 9 Manual.Count131072.C013661.packed 128 cuts13661 = true := by
 decide +kernel
def pointBounds13661 : List (Nat × Nat × Nat) := [(1794560000,95039369197598,95039746390406),(1794616320,95039793937931,95040171131037)]
theorem point_links_checked13661 : (cuts13661.take 2).map (fun c => (1794506753-1+2*2^9*c.k,95038980363175+c.lower,95039357555710+c.upper)) = pointBounds13661 := by
 decide +kernel
def cuts13662 : List PrefixCut := [⟨34,259100752,259100932⟩,
⟨89,671581284,671581753⟩,
⟨128,965798951,965799627⟩]
theorem checked13662 : checkPrefixCuts (2^48) 1794637825 9 Manual.Count131072.C013662.packed 128 cuts13662 = true := by
 decide +kernel
def pointBounds13662 : List (Nat × Nat × Nat) := [(1794672640,95040208156513,95040585349906),(1794728960,95040620637045,95040997830727)]
theorem point_links_checked13662 : (cuts13662.take 2).map (fun c => (1794637825-1+2*2^9*c.k,95039949055761+c.lower,95040326248974+c.upper)) = pointBounds13662 := by
 decide +kernel
def cuts13663 : List PrefixCut := [⟨16,118720287,118720371⟩,
⟨71,539957068,539957445⟩,
⟨126,967767143,967767813⟩,
⟨128,983292258,983292939⟩]
theorem checked13663 : checkPrefixCuts (2^48) 1794768897 9 Manual.Count131072.C013663.packed 128 cuts13663 = true := by
 decide +kernel
def pointBounds13663 : List (Nat × Nat × Nat) := [(1794785280,95041033574999,95041410768972),(1794841600,95041454811780,95041832006046),(1794897920,95041882621855,95042259816414)]
theorem point_links_checked13663 : (cuts13663.take 3).map (fun c => (1794768897-1+2*2^9*c.k,95040914854712+c.lower,95041292048601+c.upper)) = pointBounds13663 := by
 decide +kernel
def cuts13664 : List PrefixCut := [⟨53,396903535,396903814⟩,
⟨108,812925967,812926539⟩,
⟨128,959228482,959229159⟩]
theorem checked13664 : checkPrefixCuts (2^48) 1794899969 9 Manual.Count131072.C013664.packed 128 cuts13664 = true := by
 decide +kernel
def pointBounds13664 : List (Nat × Nat × Nat) := [(1794954240,95042295050505,95042672245354),(1795010560,95042711072937,95043088268079)]
theorem point_links_checked13664 : (cuts13664.take 2).map (fun c => (1794899969-1+2*2^9*c.k,95041898146970+c.lower,95042275341540+c.upper)) = pointBounds13664 := by
 decide +kernel
def cuts13665 : List PrefixCut := [⟨35,266413822,266414009⟩,
⟨90,686643676,686644162⟩,
⟨128,967782569,967783254⟩]
theorem checked13665 : checkPrefixCuts (2^48) 1795031041 9 Manual.Count131072.C013665.packed 128 cuts13665 = true := by
 decide +kernel
def pointBounds13665 : List (Nat × Nat × Nat) := [(1795066880,95043123789274,95043500984708),(1795123200,95043544019128,95043921214861)]
theorem point_links_checked13665 : (cuts13665.take 2).map (fun c => (1795031041-1+2*2^9*c.k,95042857375452+c.lower,95043234570699+c.upper)) = pointBounds13665 := by
 decide +kernel
def cuts13666 : List PrefixCut := [⟨17,126220452,126220541⟩,
⟨72,541877051,541877434⟩,
⟨127,957207032,957207704⟩,
⟨128,966457344,966458023⟩]
theorem checked13666 : checkPrefixCuts (2^48) 1795162113 9 Manual.Count131072.C013666.packed 128 cuts13666 = true := by
 decide +kernel
def pointBounds13666 : List (Nat × Nat × Nat) := [(1795179520,95043951378473,95044328574494),(1795235840,95044367035072,95044744231387),(1795292160,95044782365053,95045159561657)]
theorem point_links_checked13666 : (cuts13666.take 3).map (fun c => (1795162113-1+2*2^9*c.k,95043825158021+c.lower,95044202353953+c.upper)) = pointBounds13666 := by
 decide +kernel
def cuts13667 : List PrefixCut := [⟨54,408575195,408575485⟩,
⟨109,817764708,817765286⟩,
⟨128,961213199,961213876⟩]
theorem checked13667 : checkPrefixCuts (2^48) 1795293185 9 Manual.Count131072.C013667.packed 128 cuts13667 = true := by
 decide +kernel
def pointBounds13667 : List (Nat × Nat × Nat) := [(1795348480,95045200190560,95045577387461),(1795404800,95045609380073,95045986577262)]
theorem point_links_checked13667 : (cuts13667.take 2).map (fun c => (1795293185-1+2*2^9*c.k,95044791615365+c.lower,95045168811976+c.upper)) = pointBounds13667 := by
 decide +kernel
def cuts13668 : List PrefixCut := [⟨36,277956507,277956702⟩,
⟨91,688688058,688688547⟩,
⟨128,966159740,966160423⟩]
theorem checked13668 : checkPrefixCuts (2^48) 1795424257 9 Manual.Count131072.C013668.packed 128 cuts13668 = true := by
 decide +kernel
def pointBounds13668 : List (Nat × Nat × Nat) := [(1795461120,95046030785071,95046407982554),(1795517440,95046441516622,95046818714399)]
theorem point_links_checked13668 : (cuts13668.take 2).map (fun c => (1795424257-1+2*2^9*c.k,95045752828564+c.lower,95046130025852+c.upper)) = pointBounds13668 := by
 decide +kernel
def cuts13669 : List PrefixCut := [⟨18,136068741,136068837⟩,
⟨73,547401665,547402054⟩,
⟨128,962013487,962014169⟩]
theorem checked13669 : checkPrefixCuts (2^48) 1795555329 9 Manual.Count131072.C013669.packed 128 cuts13669 = true := by
 decide +kernel
def pointBounds13669 : List (Nat × Nat × Nat) := [(1795573760,95046855057045,95047232255112),(1795630080,95047266389969,95047643588329),(1795686400,95047681001791,95048058200444)]
theorem point_links_checked13669 : (cuts13669.take 3).map (fun c => (1795555329-1+2*2^9*c.k,95046718988304+c.lower,95047096186275+c.upper)) = pointBounds13669 := by
 decide +kernel
def cuts13670 : List PrefixCut := [⟨55,409112546,409112838⟩,
⟨110,826519704,826520284⟩,
⟨128,962099735,962100411⟩]
theorem checked13670 : checkPrefixCuts (2^48) 1795686401 9 Manual.Count131072.C013670.packed 128 cuts13670 = true := by
 decide +kernel
def pointBounds13670 : List (Nat × Nat × Nat) := [(1795742720,95048090114337,95048467313282),(1795799040,95048507521495,95048884720728)]
theorem point_links_checked13670 : (cuts13670.take 2).map (fun c => (1795686401-1+2*2^9*c.k,95047681001791+c.lower,95048058200444+c.upper)) = pointBounds13670 := by
 decide +kernel
def cuts13671 : List PrefixCut := [⟨37,282754458,282754658⟩,
⟨92,699665256,699665752⟩,
⟨128,970336770,970337455⟩]
theorem checked13671 : checkPrefixCuts (2^48) 1795817473 9 Manual.Count131072.C013671.packed 128 cuts13671 = true := by
 decide +kernel
def pointBounds13671 : List (Nat × Nat × Nat) := [(1795855360,95048925855984,95049303055513),(1795911680,95049342766782,95049719966607)]
theorem point_links_checked13671 : (cuts13671.take 2).map (fun c => (1795817473-1+2*2^9*c.k,95048643101526+c.lower,95049020300855+c.upper)) = pointBounds13671 := by
 decide +kernel
def cuts13672 : List PrefixCut := [⟨19,144658860,144658960⟩,
⟨74,558095594,558095979⟩,
⟨128,969795555,969796233⟩]
theorem checked13672 : checkPrefixCuts (2^48) 1795948545 9 Manual.Count131072.C013672.packed 128 cuts13672 = true := by
 decide +kernel
def pointBounds13672 : List (Nat × Nat × Nat) := [(1795968000,95049758097156,95050135297270),(1796024320,95050171533890,95050548734289)]
theorem point_links_checked13672 : (cuts13672.take 2).map (fun c => (1795948545-1+2*2^9*c.k,95049613438296+c.lower,95049990638310+c.upper)) = pointBounds13672 := by
 decide +kernel
def cuts13673 : List PrefixCut := [⟨1,7679094,7679100⟩,
⟨56,425321087,425321382⟩,
⟨111,842949999,842950584⟩,
⟨128,968941280,968941953⟩]
theorem checked13673 : checkPrefixCuts (2^48) 1796079617 9 Manual.Count131072.C013673.packed 128 cuts13673 = true := by
 decide +kernel
def pointBounds13673 : List (Nat × Nat × Nat) := [(1796080640,95050590912945,95050968113643),(1796136960,95051008554938,95051385755925),(1796193280,95051426183850,95051803385127)]
theorem point_links_checked13673 : (cuts13673.take 3).map (fun c => (1796079617-1+2*2^9*c.k,95050583233851+c.lower,95050960434543+c.upper)) = pointBounds13673 := by
 decide +kernel
def cuts13674 : List PrefixCut := [⟨38,285669751,285669952⟩,
⟨93,700608690,700609178⟩,
⟨128,966833412,966834086⟩]
theorem checked13674 : checkPrefixCuts (2^48) 1796210689 9 Manual.Count131072.C013674.packed 128 cuts13674 = true := by
 decide +kernel
def pointBounds13674 : List (Nat × Nat × Nat) := [(1796249600,95051837844882,95052215046448),(1796305920,95052252783821,95052629985674)]
theorem point_links_checked13674 : (cuts13674.take 2).map (fun c => (1796210689-1+2*2^9*c.k,95051552175131+c.lower,95051929376496+c.upper)) = pointBounds13674 := by
 decide +kernel
def cuts13675 : List PrefixCut := [⟨20,157946036,157946146⟩,
⟨75,576619332,576619737⟩,
⟨128,976164346,976165034⟩]
theorem checked13675 : checkPrefixCuts (2^48) 1796341761 9 Manual.Count131072.C013675.packed 128 cuts13675 = true := by
 decide +kernel
def pointBounds13675 : List (Nat × Nat × Nat) := [(1796362240,95052676954579,95053054156728),(1796418560,95053095627875,95053472830319)]
theorem point_links_checked13675 : (cuts13675.take 2).map (fun c => (1796341761-1+2*2^9*c.k,95052519008543+c.lower,95052896210582+c.upper)) = pointBounds13675 := by
 decide +kernel
def cuts13676 : List PrefixCut := [⟨2,14728095,14728105⟩,
⟨57,428361540,428361845⟩,
⟨112,839631684,839632277⟩,
⟨128,957918481,957919160⟩]
theorem checked13676 : checkPrefixCuts (2^48) 1796472833 9 Manual.Count131072.C013676.packed 128 cuts13676 = true := by
 decide +kernel
def pointBounds13676 : List (Nat × Nat × Nat) := [(1796474880,95053509900984,95053887103721),(1796531200,95053923534429,95054300737461),(1796587520,95054334804573,95054712007893)]
theorem point_links_checked13676 : (cuts13676.take 3).map (fun c => (1796472833-1+2*2^9*c.k,95053495172889+c.lower,95053872375616+c.upper)) = pointBounds13676 := by
 decide +kernel
def cuts13677 : List PrefixCut := [⟨39,290150596,290150797⟩,
⟨94,699358533,699359028⟩,
⟨128,951425442,951426117⟩]
theorem checked13677 : checkPrefixCuts (2^48) 1796603905 9 Manual.Count131072.C013677.packed 128 cuts13677 = true := by
 decide +kernel
def pointBounds13677 : List (Nat × Nat × Nat) := [(1796643840,95054743241966,95055120445573),(1796700160,95055152449903,95055529653804)]
theorem point_links_checked13677 : (cuts13677.take 2).map (fun c => (1796603905-1+2*2^9*c.k,95054453091370+c.lower,95054830294776+c.upper)) = pointBounds13677 := by
 decide +kernel
def cuts13678 : List PrefixCut := [⟨21,157754761,157754870⟩,
⟨76,565997062,565997461⟩,
⟨128,961068323,961068998⟩]
theorem checked13678 : checkPrefixCuts (2^48) 1796734977 9 Manual.Count131072.C013678.packed 128 cuts13678 = true := by
 decide +kernel
def pointBounds13678 : List (Nat × Nat × Nat) := [(1796756480,95055562271573,95055939475763),(1796812800,95055970513874,95056347718354)]
theorem point_links_checked13678 : (cuts13678.take 2).map (fun c => (1796734977-1+2*2^9*c.k,95055404516812+c.lower,95055781720893+c.upper)) = pointBounds13678 := by
 decide +kernel
def cuts13679 : List PrefixCut := [⟨3,24280368,24280384⟩,
⟨58,441112594,441112899⟩,
⟨113,864197301,864197898⟩,
⟨128,977915691,977916367⟩]
theorem checked13679 : checkPrefixCuts (2^48) 1796866049 9 Manual.Count131072.C013679.packed 128 cuts13679 = true := by
 decide +kernel
def pointBounds13679 : List (Nat × Nat × Nat) := [(1796869120,95056389865503,95056767070275),(1796925440,95056806697729,95057183902790),(1796981760,95057229782436,95057606987789)]
theorem point_links_checked13679 : (cuts13679.take 3).map (fun c => (1796866049-1+2*2^9*c.k,95056365585135+c.lower,95056742789891+c.upper)) = pointBounds13679 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000114
