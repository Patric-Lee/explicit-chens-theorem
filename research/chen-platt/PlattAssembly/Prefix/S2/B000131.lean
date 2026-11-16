import PlattAssemblyKernel
import PlattCertificates.Count131072.C014192
import PlattCertificates.Count131072.C014193
import PlattCertificates.Count131072.C014194
import PlattCertificates.Count131072.C014195
import PlattCertificates.Count131072.C014196
import PlattCertificates.Count131072.C014197
import PlattCertificates.Count131072.C014198
import PlattCertificates.Count131072.C014199
import PlattCertificates.Count131072.C014200
import PlattCertificates.Count131072.C014201
import PlattCertificates.Count131072.C014202
import PlattCertificates.Count131072.C014203
import PlattCertificates.Count131072.C014204
import PlattCertificates.Count131072.C014205
import PlattCertificates.Count131072.C014206
import PlattCertificates.Count131072.C014207
import PlattCertificates.Count131072.C014208
import PlattCertificates.Count131072.C014209
import PlattCertificates.Count131072.C014210
import PlattCertificates.Count131072.C014211
import PlattCertificates.Count131072.C014212
import PlattCertificates.Count131072.C014213
import PlattCertificates.Count131072.C014214
import PlattCertificates.Count131072.C014215
import PlattCertificates.Count131072.C014216
import PlattCertificates.Count131072.C014217
import PlattCertificates.Count131072.C014218
import PlattCertificates.Count131072.C014219
import PlattCertificates.Count131072.C014220
import PlattCertificates.Count131072.C014221
import PlattCertificates.Count131072.C014222
import PlattCertificates.Count131072.C014223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000131
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14192 : List PrefixCut := [⟨37,265299484,265299663⟩,
⟨94,678866055,678866517⟩,
⟨128,922711775,922712402⟩]
theorem checked14192 : checkPrefixCuts (2^48) 1864105985 9 Manual.Count131072.C014192.packed 128 cuts14192 = true := by
 decide +kernel
def pointBounds14192 : List (Nat × Nat × Nat) := [(1864143872,95541429060335,95541806602397),(1864202240,95541842626906,95542220169251)]
theorem point_links_checked14192 : (cuts14192.take 2).map (fun c => (1864105985-1+2*2^9*c.k,95541163760851+c.lower,95541541302734+c.upper)) = pointBounds14192 := by
 decide +kernel
def cuts14193 : List PrefixCut := [⟨23,166084244,166084359⟩,
⟨80,574491558,574491959⟩,
⟨128,918570455,918571090⟩]
theorem checked14193 : checkPrefixCuts (2^48) 1864237057 9 Manual.Count131072.C014193.packed 128 cuts14193 = true := by
 decide +kernel
def pointBounds14193 : List (Nat × Nat × Nat) := [(1864260608,95542252556870,95542630099495),(1864318976,95542660964184,95543038507095)]
theorem point_links_checked14193 : (cuts14193.take 2).map (fun c => (1864237057-1+2*2^9*c.k,95542086472626+c.lower,95542464015136+c.upper)) = pointBounds14193 := by
 decide +kernel
def cuts14194 : List PrefixCut := [⟨9,62352940,62352985⟩,
⟨66,475716690,475717019⟩,
⟨123,887406984,887407597⟩,
⟨128,920619419,920620055⟩]
theorem checked14194 : checkPrefixCuts (2^48) 1864368129 9 Manual.Count131072.C014194.packed 128 cuts14194 = true := by
 decide +kernel
def pointBounds14194 : List (Nat × Nat × Nat) := [(1864377344,95543067396021,95543444939211),(1864435712,95543480759771,95543858303245),(1864494080,95543892450065,95544269993823)]
theorem point_links_checked14194 : (cuts14194.take 3).map (fun c => (1864368129-1+2*2^9*c.k,95543005043081+c.lower,95543382586226+c.upper)) = pointBounds14194 := by
 decide +kernel
def cuts14195 : List PrefixCut := [⟨52,380427405,380427669⟩,
⟨109,794960087,794960636⟩,
⟨128,930518191,930518835⟩]
theorem checked14195 : checkPrefixCuts (2^48) 1864499201 9 Manual.Count131072.C014195.packed 128 cuts14195 = true := by
 decide +kernel
def pointBounds14195 : List (Nat × Nat × Nat) := [(1864552448,95544306089905,95544683633950),(1864610816,95544720622587,95545098166917)]
theorem point_links_checked14195 : (cuts14195.take 2).map (fun c => (1864499201-1+2*2^9*c.k,95543925662500+c.lower,95544303206281+c.upper)) = pointBounds14195 := by
 decide +kernel
def cuts14196 : List PrefixCut := [⟨38,270055278,270055464⟩,
⟨95,684260153,684260624⟩,
⟨128,920188018,920188652⟩]
theorem checked14196 : checkPrefixCuts (2^48) 1864630273 9 Manual.Count131072.C014196.packed 128 cuts14196 = true := by
 decide +kernel
def pointBounds14196 : List (Nat × Nat × Nat) := [(1864669184,95545126235969,95545503780580),(1864727552,95545540440844,95545917985740)]
theorem point_links_checked14196 : (cuts14196.take 2).map (fun c => (1864630273-1+2*2^9*c.k,95544856180691+c.lower,95545233725116+c.upper)) = pointBounds14196 := by
 decide +kernel
def cuts14197 : List PrefixCut := [⟨24,173735614,173735733⟩,
⟨81,571763977,571764366⟩,
⟨128,906086174,906086799⟩]
theorem checked14197 : checkPrefixCuts (2^48) 1864761345 9 Manual.Count131072.C014197.packed 128 cuts14197 = true := by
 decide +kernel
def pointBounds14197 : List (Nat × Nat × Nat) := [(1864785920,95545950104323,95546327649501),(1864844288,95546348132686,95546725678134)]
theorem point_links_checked14197 : (cuts14197.take 2).map (fun c => (1864761345-1+2*2^9*c.k,95545776368709+c.lower,95546153913768+c.upper)) = pointBounds14197 := by
 decide +kernel
def cuts14198 : List PrefixCut := [⟨10,70032986,70033035⟩,
⟨67,493392632,493392970⟩,
⟨124,906325259,906325878⟩,
⟨128,937113580,937114220⟩]
theorem checked14198 : checkPrefixCuts (2^48) 1864892417 9 Manual.Count131072.C014198.packed 128 cuts14198 = true := by
 decide +kernel
def pointBounds14198 : List (Nat × Nat × Nat) := [(1864902656,95546752487869,95547130033602),(1864961024,95547175847515,95547553393537),(1865019392,95547588780142,95547966326445)]
theorem point_links_checked14198 : (cuts14198.take 3).map (fun c => (1864892417-1+2*2^9*c.k,95546682454883+c.lower,95547060000567+c.upper)) = pointBounds14198 := by
 decide +kernel
def cuts14199 : List PrefixCut := [⟨53,381074919,381075187⟩,
⟨110,793377984,793378533⟩,
⟨128,924521482,924522120⟩]
theorem checked14199 : checkPrefixCuts (2^48) 1865023489 9 Manual.Count131072.C014199.packed 128 cuts14199 = true := by
 decide +kernel
def pointBounds14199 : List (Nat × Nat × Nat) := [(1865077760,95548000643382,95548378189974),(1865136128,95548412946447,95548790493320)]
theorem point_links_checked14199 : (cuts14199.take 2).map (fun c => (1865023489-1+2*2^9*c.k,95547619568463+c.lower,95547997114787+c.upper)) = pointBounds14199 := by
 decide +kernel
def cuts14200 : List PrefixCut := [⟨39,284919484,284919679⟩,
⟨96,693122282,693122753⟩,
⟨128,925060302,925060928⟩]
theorem checked14200 : checkPrefixCuts (2^48) 1865154561 9 Manual.Count131072.C014200.packed 128 cuts14200 = true := by
 decide +kernel
def pointBounds14200 : List (Nat × Nat × Nat) := [(1865194496,95548829009429,95549206556586),(1865252864,95549237212227,95549614759660)]
theorem point_links_checked14200 : (cuts14200.take 2).map (fun c => (1865154561-1+2*2^9*c.k,95548544089945+c.lower,95548921636907+c.upper)) = pointBounds14200 := by
 decide +kernel
def cuts14201 : List PrefixCut := [⟨25,175497548,175497668⟩,
⟨82,590012588,590012990⟩,
⟨128,926654987,926655620⟩]
theorem checked14201 : checkPrefixCuts (2^48) 1865285633 9 Manual.Count131072.C014201.packed 128 cuts14201 = true := by
 decide +kernel
def pointBounds14201 : List (Nat × Nat × Nat) := [(1865311232,95549644647795,95550022195503),(1865369600,95550059162835,95550436710825)]
theorem point_links_checked14201 : (cuts14201.take 2).map (fun c => (1865285633-1+2*2^9*c.k,95549469150247+c.lower,95549846697835+c.upper)) = pointBounds14201 := by
 decide +kernel
def cuts14202 : List PrefixCut := [⟨11,81933642,81933698⟩,
⟨68,498082356,498082698⟩,
⟨125,904863417,904864037⟩,
⟨128,926590234,926590870⟩]
theorem checked14202 : checkPrefixCuts (2^48) 1865416705 9 Manual.Count131072.C014202.packed 128 cuts14202 = true := by
 decide +kernel
def pointBounds14202 : List (Nat × Nat × Nat) := [(1865427968,95550477738876,95550855287153),(1865486336,95550893887590,95551271436153),(1865544704,95551300668651,95551678217492)]
theorem point_links_checked14202 : (cuts14202.take 3).map (fun c => (1865416705-1+2*2^9*c.k,95550395805234+c.lower,95550773353455+c.upper)) = pointBounds14202 := by
 decide +kernel
def cuts14203 : List PrefixCut := [⟨54,384739758,384740025⟩,
⟨111,787421734,787422282⟩,
⟨128,910230472,910231105⟩]
theorem checked14203 : checkPrefixCuts (2^48) 1865547777 9 Manual.Count131072.C014203.packed 128 cuts14203 = true := by
 decide +kernel
def pointBounds14203 : List (Nat × Nat × Nat) := [(1865603072,95551707135226,95552084684350),(1865661440,95552109817202,95552487366607)]
theorem point_links_checked14203 : (cuts14203.take 2).map (fun c => (1865547777-1+2*2^9*c.k,95551322395468+c.lower,95551699944325+c.upper)) = pointBounds14203 := by
 decide +kernel
def cuts14204 : List PrefixCut := [⟨40,288761932,288762131⟩,
⟨97,704091328,704091811⟩,
⟨128,932041731,932042372⟩]
theorem checked14204 : checkPrefixCuts (2^48) 1865678849 9 Manual.Count131072.C014204.packed 128 cuts14204 = true := by
 decide +kernel
def pointBounds14204 : List (Nat × Nat × Nat) := [(1865719808,95552521387872,95552898937561),(1865778176,95552936717268,95553314267241)]
theorem point_links_checked14204 : (cuts14204.take 2).map (fun c => (1865678849-1+2*2^9*c.k,95552232625940+c.lower,95552610175430+c.upper)) = pointBounds14204 := by
 decide +kernel
def cuts14205 : List PrefixCut := [⟨26,189025420,189025552⟩,
⟨83,598294551,598294960⟩,
⟨128,918701231,918701858⟩]
theorem checked14205 : checkPrefixCuts (2^48) 1865809921 9 Manual.Count131072.C014205.packed 128 cuts14205 = true := by
 decide +kernel
def pointBounds14205 : List (Nat × Nat × Nat) := [(1865836544,95553353693091,95553731243354),(1865894912,95553762962222,95554140512762)]
theorem point_links_checked14205 : (cuts14205.take 2).map (fun c => (1865809921-1+2*2^9*c.k,95553164667671+c.lower,95553542217802+c.upper)) = pointBounds14205 := by
 decide +kernel
def cuts14206 : List PrefixCut := [⟨12,89905566,89905627⟩,
⟨69,497338945,497339287⟩,
⟨126,914111742,914112367⟩,
⟨128,930402272,930402908⟩]
theorem checked14206 : checkPrefixCuts (2^48) 1865940993 9 Manual.Count131072.C014206.packed 128 cuts14206 = true := by
 decide +kernel
def pointBounds14206 : List (Nat × Nat × Nat) := [(1865953280,95554173274468,95554550825287),(1866011648,95554580707847,95554958258947),(1866070016,95554997480644,95555375032027)]
theorem point_links_checked14206 : (cuts14206.take 3).map (fun c => (1865940993-1+2*2^9*c.k,95554083368902+c.lower,95554460919660+c.upper)) = pointBounds14206 := by
 decide +kernel
def cuts14207 : List PrefixCut := [⟨55,391720710,391720976⟩,
⟨112,800775004,800775553⟩,
⟨128,917516055,917516687⟩]
theorem checked14207 : checkPrefixCuts (2^48) 1866072065 9 Manual.Count131072.C014207.packed 128 cuts14207 = true := by
 decide +kernel
def pointBounds14207 : List (Nat × Nat × Nat) := [(1866128384,95555405491884,95555783043544),(1866186752,95555814546178,95556192098121)]
theorem point_links_checked14207 : (cuts14207.take 2).map (fun c => (1866072065-1+2*2^9*c.k,95555013771174+c.lower,95555391322568+c.upper)) = pointBounds14207 := by
 decide +kernel
def cuts14208 : List PrefixCut := [⟨41,291697280,291697478⟩,
⟨98,702837620,702838103⟩,
⟨128,918356853,918357484⟩]
theorem checked14208 : checkPrefixCuts (2^48) 1866203137 9 Manual.Count131072.C014208.packed 128 cuts14208 = true := by
 decide +kernel
def pointBounds14208 : List (Nat × Nat × Nat) := [(1866245120,95556222984509,95556600536733),(1866303488,95556634124849,95557011677358)]
theorem point_links_checked14208 : (cuts14208.take 2).map (fun c => (1866203137-1+2*2^9*c.k,95555931287229+c.lower,95556308839255+c.upper)) = pointBounds14208 := by
 decide +kernel
def cuts14209 : List PrefixCut := [⟨27,193949201,193949333⟩,
⟨84,607476758,607477175⟩,
⟨128,930960334,930960971⟩]
theorem checked14209 : checkPrefixCuts (2^48) 1866334209 9 Manual.Count131072.C014209.packed 128 cuts14209 = true := by
 decide +kernel
def pointBounds14209 : List (Nat × Nat × Nat) := [(1866361856,95557043593283,95557421146072),(1866420224,95557457120840,95557834673914)]
theorem point_links_checked14209 : (cuts14209.take 2).map (fun c => (1866334209-1+2*2^9*c.k,95556849644082+c.lower,95557227196739+c.upper)) = pointBounds14209 := by
 decide +kernel
def cuts14210 : List PrefixCut := [⟨13,94555266,94555334⟩,
⟨70,508509393,508509741⟩,
⟨127,928180877,928181512⟩,
⟨128,935720669,935721309⟩]
theorem checked14210 : checkPrefixCuts (2^48) 1866465281 9 Manual.Count131072.C014210.packed 128 cuts14210 = true := by
 decide +kernel
def pointBounds14210 : List (Nat × Nat × Nat) := [(1866478592,95557875159682,95558252713044),(1866536960,95558289113809,95558666667451),(1866595328,95558708785293,95559086339222)]
theorem point_links_checked14210 : (cuts14210.take 3).map (fun c => (1866465281-1+2*2^9*c.k,95557780604416+c.lower,95558158157710+c.upper)) = pointBounds14210 := by
 decide +kernel
def cuts14211 : List PrefixCut := [⟨56,410610659,410610940⟩,
⟨113,827390857,827391423⟩,
⟨128,938972380,938973024⟩]
theorem checked14211 : checkPrefixCuts (2^48) 1866596353 9 Manual.Count131072.C014211.packed 128 cuts14211 = true := by
 decide +kernel
def pointBounds14211 : List (Nat × Nat × Nat) := [(1866653696,95559126935744,95559504489959),(1866712064,95559543715942,95559921270442)]
theorem point_links_checked14211 : (cuts14211.take 2).map (fun c => (1866596353-1+2*2^9*c.k,95558716325085+c.lower,95559093879019+c.upper)) = pointBounds14211 := by
 decide +kernel
def cuts14212 : List PrefixCut := [⟨42,305638093,305638304⟩,
⟨99,715305633,715306125⟩,
⟨128,923979357,923979996⟩]
theorem checked14212 : checkPrefixCuts (2^48) 1866727425 9 Manual.Count131072.C014212.packed 128 cuts14212 = true := by
 decide +kernel
def pointBounds14212 : List (Nat × Nat × Nat) := [(1866770432,95559960935558,95560338490347),(1866828800,95560370603098,95560748158168)]
theorem point_links_checked14212 : (cuts14212.take 2).map (fun c => (1866727425-1+2*2^9*c.k,95559655297465+c.lower,95560032852043+c.upper)) = pointBounds14212 := by
 decide +kernel
def cuts14213 : List PrefixCut := [⟨28,206408862,206409006⟩,
⟨85,615749271,615749702⟩,
⟨128,931905164,931905813⟩]
theorem checked14213 : checkPrefixCuts (2^48) 1866858497 9 Manual.Count131072.C014213.packed 128 cuts14213 = true := by
 decide +kernel
def pointBounds14213 : List (Nat × Nat × Nat) := [(1866887168,95560785685684,95561163241045),(1866945536,95561195026093,95561572581741)]
theorem point_links_checked14213 : (cuts14213.take 2).map (fun c => (1866858497-1+2*2^9*c.k,95560579276822+c.lower,95560956832039+c.upper)) = pointBounds14213 := by
 decide +kernel
def cuts14214 : List PrefixCut := [⟨14,100709989,100710057⟩,
⟨71,505200414,505200756⟩,
⟨128,924603020,924603651⟩]
theorem checked14214 : checkPrefixCuts (2^48) 1866989569 9 Manual.Count131072.C014214.packed 128 cuts14214 = true := by
 decide +kernel
def pointBounds14214 : List (Nat × Nat × Nat) := [(1867003904,95561611891975,95561989447909),(1867062272,95562016382400,95562393938608),(1867120640,95562435785006,95562813341503)]
theorem point_links_checked14214 : (cuts14214.take 3).map (fun c => (1866989569-1+2*2^9*c.k,95561511181986+c.lower,95561888737852+c.upper)) = pointBounds14214 := by
 decide +kernel
def cuts14215 : List PrefixCut := [⟨57,401902446,401902723⟩,
⟨114,808616297,808616851⟩,
⟨128,908257713,908258336⟩]
theorem checked14215 : checkPrefixCuts (2^48) 1867120641 9 Manual.Count131072.C014215.packed 128 cuts14215 = true := by
 decide +kernel
def pointBounds14215 : List (Nat × Nat × Nat) := [(1867179008,95562837687452,95563215244226),(1867237376,95563244401303,95563621958354)]
theorem point_links_checked14215 : (cuts14215.take 2).map (fun c => (1867120641-1+2*2^9*c.k,95562435785006+c.lower,95562813341503+c.upper)) = pointBounds14215 := by
 decide +kernel
def cuts14216 : List PrefixCut := [⟨43,304346227,304346437⟩,
⟨100,722038312,722038811⟩,
⟨128,921157196,921157834⟩]
theorem checked14216 : checkPrefixCuts (2^48) 1867251713 9 Manual.Count131072.C014216.packed 128 cuts14216 = true := by
 decide +kernel
def pointBounds14216 : List (Nat × Nat × Nat) := [(1867295744,95563648388946,95564025946276),(1867354112,95564066081031,95564443638650)]
theorem point_links_checked14216 : (cuts14216.take 2).map (fun c => (1867251713-1+2*2^9*c.k,95563344042719+c.lower,95563721599839+c.upper)) = pointBounds14216 := by
 decide +kernel
def cuts14217 : List PrefixCut := [⟨29,207405940,207406085⟩,
⟨86,618289189,618289618⟩,
⟨128,925312841,925313482⟩]
theorem checked14217 : checkPrefixCuts (2^48) 1867382785 9 Manual.Count131072.C014217.packed 128 cuts14217 = true := by
 decide +kernel
def pointBounds14217 : List (Nat × Nat × Nat) := [(1867412480,95564472605855,95564850163758),(1867470848,95564883489104,95565261047291)]
theorem point_links_checked14217 : (cuts14217.take 2).map (fun c => (1867382785-1+2*2^9*c.k,95564265199915+c.lower,95564642757673+c.upper)) = pointBounds14217 := by
 decide +kernel
def cuts14218 : List PrefixCut := [⟨15,108971337,108971413⟩,
⟨72,523747586,523747941⟩,
⟨128,923741124,923741754⟩]
theorem checked14218 : checkPrefixCuts (2^48) 1867513857 9 Manual.Count131072.C014218.packed 128 cuts14218 = true := by
 decide +kernel
def pointBounds14218 : List (Nat × Nat × Nat) := [(1867529216,95565299484093,95565677042568),(1867587584,95565714260342,95566091819096)]
theorem point_links_checked14218 : (cuts14218.take 2).map (fun c => (1867513857-1+2*2^9*c.k,95565190512756+c.lower,95565568071155+c.upper)) = pointBounds14218 := by
 decide +kernel
def cuts14219 : List PrefixCut := [⟨1,6781999,6782004⟩,
⟨58,418819593,418819878⟩,
⟨115,835666808,835667379⟩,
⟨128,931361995,931362632⟩]
theorem checked14219 : checkPrefixCuts (2^48) 1867644929 9 Manual.Count131072.C014219.packed 128 cuts14219 = true := by
 decide +kernel
def pointBounds14219 : List (Nat × Nat × Nat) := [(1867645952,95566121035879,95566498594913),(1867704320,95566533073473,95566910632787),(1867762688,95566949920688,95567327480288)]
theorem point_links_checked14219 : (cuts14219.take 3).map (fun c => (1867644929-1+2*2^9*c.k,95566114253880+c.lower,95566491812909+c.upper)) = pointBounds14219 := by
 decide +kernel
def cuts14220 : List PrefixCut := [⟨44,308178855,308179067⟩,
⟨102,732233311,732233812⟩,
⟨128,916679155,916679782⟩]
theorem checked14220 : checkPrefixCuts (2^48) 1867776001 9 Manual.Count131072.C014220.packed 128 cuts14220 = true := by
 decide +kernel
def pointBounds14220 : List (Nat × Nat × Nat) := [(1867821056,95567353794730,95567731354608),(1867880448,95567777849186,95568155409353)]
theorem point_links_checked14220 : (cuts14220.take 2).map (fun c => (1867776001-1+2*2^9*c.k,95567045615875+c.lower,95567423175541+c.upper)) = pointBounds14220 := by
 decide +kernel
def cuts14221 : List PrefixCut := [⟨32,231457776,231457936⟩,
⟨90,647800194,647800644⟩,
⟨128,920231375,920232017⟩]
theorem checked14221 : checkPrefixCuts (2^48) 1867907073 9 Manual.Count131072.C014221.packed 128 cuts14221 = true := by
 decide +kernel
def pointBounds14221 : List (Nat × Nat × Nat) := [(1867939840,95568193752806,95568571313259),(1867999232,95568610095224,95568987655967)]
theorem point_links_checked14221 : (cuts14221.take 2).map (fun c => (1867907073-1+2*2^9*c.k,95567962295030+c.lower,95568339855323+c.upper)) = pointBounds14221 := by
 decide +kernel
def cuts14222 : List PrefixCut := [⟨20,149925192,149925296⟩,
⟨78,564734398,564734785⟩,
⟨128,926043157,926043792⟩]
theorem checked14222 : checkPrefixCuts (2^48) 1868038145 9 Manual.Count131072.C014222.packed 128 cuts14222 = true := by
 decide +kernel
def pointBounds14222 : List (Nat × Nat × Nat) := [(1868058624,95569032451597,95569410012636),(1868118016,95569447260803,95569824822125)]
theorem point_links_checked14222 : (cuts14222.take 2).map (fun c => (1868038145-1+2*2^9*c.k,95568882526405+c.lower,95569260087340+c.upper)) = pointBounds14222 := by
 decide +kernel
def cuts14223 : List PrefixCut := [⟨8,56952697,56952735⟩,
⟨66,473242265,473242586⟩,
⟨124,892531770,892532378⟩,
⟨128,921910163,921910791⟩]
theorem checked14223 : checkPrefixCuts (2^48) 1868169217 9 Manual.Count131072.C014223.packed 128 cuts14223 = true := by
 decide +kernel
def pointBounds14223 : List (Nat × Nat × Nat) := [(1868177408,95569865522259,95570243083867),(1868236800,95570281811827,95570659373718),(1868296192,95570701101332,95571078663510)]
theorem point_links_checked14223 : (cuts14223.take 3).map (fun c => (1868169217-1+2*2^9*c.k,95569808569562+c.lower,95570186131132+c.upper)) = pointBounds14223 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000131
