import PlattAssemblyKernel
import PlattCertificates.Count131072.C013552
import PlattCertificates.Count131072.C013553
import PlattCertificates.Count131072.C013554
import PlattCertificates.Count131072.C013555
import PlattCertificates.Count131072.C013556
import PlattCertificates.Count131072.C013557
import PlattCertificates.Count131072.C013558
import PlattCertificates.Count131072.C013559
import PlattCertificates.Count131072.C013560
import PlattCertificates.Count131072.C013561
import PlattCertificates.Count131072.C013562
import PlattCertificates.Count131072.C013563
import PlattCertificates.Count131072.C013564
import PlattCertificates.Count131072.C013565
import PlattCertificates.Count131072.C013566
import PlattCertificates.Count131072.C013567
import PlattCertificates.Count131072.C013568
import PlattCertificates.Count131072.C013569
import PlattCertificates.Count131072.C013570
import PlattCertificates.Count131072.C013571
import PlattCertificates.Count131072.C013572
import PlattCertificates.Count131072.C013573
import PlattCertificates.Count131072.C013574
import PlattCertificates.Count131072.C013575
import PlattCertificates.Count131072.C013576
import PlattCertificates.Count131072.C013577
import PlattCertificates.Count131072.C013578
import PlattCertificates.Count131072.C013579
import PlattCertificates.Count131072.C013580
import PlattCertificates.Count131072.C013581
import PlattCertificates.Count131072.C013582
import PlattCertificates.Count131072.C013583
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000111
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13552 : List PrefixCut := [⟨34,261831649,261831837⟩,
⟨89,681289085,681289565⟩,
⟨128,982474441,982475132⟩]
theorem checked13552 : checkPrefixCuts (2^48) 1780219905 9 Manual.Count131072.C013552.packed 128 cuts13552 = true := by
 decide +kernel
def pointBounds13552 : List (Nat × Nat × Nat) := [(1780254720,94933624243969,94934001362216),(1780311040,94934043701405,94934420819944)]
theorem point_links_checked13552 : (cuts13552.take 2).map (fun c => (1780219905-1+2*2^9*c.k,94933362412320+c.lower,94933739530379+c.upper)) = pointBounds13552 := by
 decide +kernel
def cuts13553 : List PrefixCut := [⟨16,127586739,127586828⟩,
⟨71,541484239,541484618⟩,
⟨126,958214256,958214930⟩,
⟨128,972916554,972917239⟩]
theorem checked13553 : checkPrefixCuts (2^48) 1780350977 9 Manual.Count131072.C013553.packed 128 cuts13553 = true := by
 decide +kernel
def pointBounds13553 : List (Nat × Nat × Nat) := [(1780367360,94934472473500,94934849592339),(1780423680,94934886371000,94935263490129),(1780480000,94935303101017,94935680220441)]
theorem point_links_checked13553 : (cuts13553.take 3).map (fun c => (1780350977-1+2*2^9*c.k,94934344886761+c.lower,94934722005511+c.upper)) = pointBounds13553 := by
 decide +kernel
def cuts13554 : List PrefixCut := [⟨53,394426376,394426652⟩,
⟨108,811604326,811604892⟩,
⟨128,966363117,966363793⟩]
theorem checked13554 : checkPrefixCuts (2^48) 1780482049 9 Manual.Count131072.C013554.packed 128 cuts13554 = true := by
 decide +kernel
def pointBounds13554 : List (Nat × Nat × Nat) := [(1780536320,94935712229691,94936089349402),(1780592640,94936129407641,94936506527642)]
theorem point_links_checked13554 : (cuts13554.take 2).map (fun c => (1780482049-1+2*2^9*c.k,94935317803315+c.lower,94935694922750+c.upper)) = pointBounds13554 := by
 decide +kernel
def cuts13555 : List PrefixCut := [⟨35,262564105,262564290⟩,
⟨90,677976886,677977362⟩,
⟨128,969927778,969928461⟩]
theorem checked13555 : checkPrefixCuts (2^48) 1780613121 9 Manual.Count131072.C013555.packed 128 cuts13555 = true := by
 decide +kernel
def pointBounds13555 : List (Nat × Nat × Nat) := [(1780648960,94936546730537,94936923850833),(1780705280,94936962143318,94937339263905)]
theorem point_links_checked13555 : (cuts13555.take 2).map (fun c => (1780613121-1+2*2^9*c.k,94936284166432+c.lower,94936661286543+c.upper)) = pointBounds13555 := by
 decide +kernel
def cuts13556 : List PrefixCut := [⟨17,130877884,130877976⟩,
⟨72,558909222,558909613⟩,
⟨127,981553151,981553840⟩,
⟨128,988349485,988350179⟩]
theorem checked13556 : checkPrefixCuts (2^48) 1780744193 9 Manual.Count131072.C013556.packed 128 cuts13556 = true := by
 decide +kernel
def pointBounds13556 : List (Nat × Nat × Nat) := [(1780761600,94937384972094,94937762092980),(1780817920,94937813003432,94938190124617),(1780874240,94938235647361,94938612768844)]
theorem point_links_checked13556 : (cuts13556.take 3).map (fun c => (1780744193-1+2*2^9*c.k,94937254094210+c.lower,94937631215004+c.upper)) = pointBounds13556 := by
 decide +kernel
def cuts13557 : List PrefixCut := [⟨54,402241809,402242093⟩,
⟨109,824859064,824859646⟩,
⟨128,967098174,967098854⟩]
theorem checked13557 : checkPrefixCuts (2^48) 1780875265 9 Manual.Count131072.C013557.packed 128 cuts13557 = true := by
 decide +kernel
def pointBounds13557 : List (Nat × Nat × Nat) := [(1780930560,94938644685504,94939021807276),(1780986880,94939067302759,94939444424829)]
theorem point_links_checked13557 : (cuts13557.take 2).map (fun c => (1780875265-1+2*2^9*c.k,94938242443695+c.lower,94938619565183+c.upper)) = pointBounds13557 := by
 decide +kernel
def cuts13558 : List PrefixCut := [⟨36,271988489,271988679⟩,
⟨91,687467300,687467782⟩,
⟨128,967343182,967343862⟩]
theorem checked13558 : checkPrefixCuts (2^48) 1781006337 9 Manual.Count131072.C013558.packed 128 cuts13558 = true := by
 decide +kernel
def pointBounds13558 : List (Nat × Nat × Nat) := [(1781043200,94939481530358,94939858652716),(1781099520,94939897009169,94940274131819)]
theorem point_links_checked13558 : (cuts13558.take 2).map (fun c => (1781006337-1+2*2^9*c.k,94939209541869+c.lower,94939586664037+c.upper)) = pointBounds13558 := by
 decide +kernel
def cuts13559 : List PrefixCut := [⟨18,134799733,134799832⟩,
⟨73,543457104,543457491⟩,
⟨128,964901374,964902061⟩]
theorem checked13559 : checkPrefixCuts (2^48) 1781137409 9 Manual.Count131072.C013559.packed 128 cuts13559 = true := by
 decide +kernel
def pointBounds13559 : List (Nat × Nat × Nat) := [(1781155840,94940311684784,94940688807731),(1781212160,94940720342155,94941097465390),(1781268480,94941141786425,94941518909960)]
theorem point_links_checked13559 : (cuts13559.take 3).map (fun c => (1781137409-1+2*2^9*c.k,94940176885051+c.lower,94940554007899+c.upper)) = pointBounds13559 := by
 decide +kernel
def cuts13560 : List PrefixCut := [⟨55,423169111,423169412⟩,
⟨110,836054121,836054717⟩,
⟨128,973047526,973048222⟩]
theorem checked13560 : checkPrefixCuts (2^48) 1781268481 9 Manual.Count131072.C013560.packed 128 cuts13560 = true := by
 decide +kernel
def pointBounds13560 : List (Nat × Nat × Nat) := [(1781324800,94941564955536,94941942079372),(1781381120,94941977840546,94942354964677)]
theorem point_links_checked13560 : (cuts13560.take 2).map (fun c => (1781268481-1+2*2^9*c.k,94941141786425+c.lower,94941518909960+c.upper)) = pointBounds13560 := by
 decide +kernel
def cuts13561 : List PrefixCut := [⟨37,279038652,279038852⟩,
⟨92,695689578,695690069⟩,
⟨128,974081564,974082255⟩]
theorem checked13561 : checkPrefixCuts (2^48) 1781399553 9 Manual.Count131072.C013561.packed 128 cuts13561 = true := by
 decide +kernel
def pointBounds13561 : List (Nat × Nat × Nat) := [(1781437440,94942393872603,94942770997034),(1781493760,94942810523529,94943187648251)]
theorem point_links_checked13561 : (cuts13561.take 2).map (fun c => (1781399553-1+2*2^9*c.k,94942114833951+c.lower,94942491958182+c.upper)) = pointBounds13561 := by
 decide +kernel
def cuts13562 : List PrefixCut := [⟨19,145197640,145197738⟩,
⟨74,557872451,557872840⟩,
⟨128,967848554,967849234⟩]
theorem checked13562 : checkPrefixCuts (2^48) 1781530625 9 Manual.Count131072.C013562.packed 128 cuts13562 = true := by
 decide +kernel
def pointBounds13562 : List (Nat × Nat × Nat) := [(1781550080,94943234113155,94943611238175),(1781606400,94943646787966,94944023913277)]
theorem point_links_checked13562 : (cuts13562.take 2).map (fun c => (1781530625-1+2*2^9*c.k,94943088915515+c.lower,94943466040437+c.upper)) = pointBounds13562 := by
 decide +kernel
def cuts13563 : List PrefixCut := [⟨1,7425268,7425273⟩,
⟨56,424497475,424497770⟩,
⟨111,841082499,841083092⟩,
⟨128,973306412,973307099⟩]
theorem checked13563 : checkPrefixCuts (2^48) 1781661697 9 Manual.Count131072.C013563.packed 128 cuts13563 = true := by
 decide +kernel
def pointBounds13563 : List (Nat × Nat × Nat) := [(1781662720,94944064189337,94944441314944),(1781719040,94944481261544,94944858387441),(1781775360,94944897846568,94945274972763)]
theorem point_links_checked13563 : (cuts13563.take 3).map (fun c => (1781661697-1+2*2^9*c.k,94944056764069+c.lower,94944433889671+c.upper)) = pointBounds13563 := by
 decide +kernel
def cuts13564 : List PrefixCut := [⟨38,284347994,284348198⟩,
⟨93,703592154,703592656⟩,
⟨128,957754311,957754995⟩]
theorem checked13564 : checkPrefixCuts (2^48) 1781792769 9 Manual.Count131072.C013564.packed 128 cuts13564 = true := by
 decide +kernel
def pointBounds13564 : List (Nat × Nat × Nat) := [(1781831680,94945314418475,94945691544968),(1781888000,94945733662635,94946110789426)]
theorem point_links_checked13564 : (cuts13564.take 2).map (fun c => (1781792769-1+2*2^9*c.k,94945030070481+c.lower,94945407196770+c.upper)) = pointBounds13564 := by
 decide +kernel
def cuts13565 : List PrefixCut := [⟨20,152431703,152431810⟩,
⟨75,574018757,574019166⟩,
⟨128,970162355,970163044⟩]
theorem checked13565 : checkPrefixCuts (2^48) 1781923841 9 Manual.Count131072.C013565.packed 128 cuts13565 = true := by
 decide +kernel
def pointBounds13565 : List (Nat × Nat × Nat) := [(1781944320,94946140256495,94946517383575),(1782000640,94946561843549,94946938970931)]
theorem point_links_checked13565 : (cuts13565.take 2).map (fun c => (1781923841-1+2*2^9*c.k,94945987824792+c.lower,94946364951765+c.upper)) = pointBounds13565 := by
 decide +kernel
def cuts13566 : List PrefixCut := [⟨2,14215456,14215466⟩,
⟨57,434670228,434670533⟩,
⟨112,850689278,850689874⟩,
⟨128,978303752,978304436⟩]
theorem checked13566 : checkPrefixCuts (2^48) 1782054913 9 Manual.Count131072.C013566.packed 128 cuts13566 = true := by
 decide +kernel
def pointBounds13566 : List (Nat × Nat × Nat) := [(1782056960,94946972202603,94947349330275),(1782113280,94947392657375,94947769785342),(1782169600,94947808676425,94948185804683)]
theorem point_links_checked13566 : (cuts13566.take 3).map (fun c => (1782054913-1+2*2^9*c.k,94946957987147+c.lower,94947335114809+c.upper)) = pointBounds13566 := by
 decide +kernel
def cuts13567 : List PrefixCut := [⟨39,290918544,290918748⟩,
⟨94,704384417,704384913⟩,
⟨128,960385599,960386279⟩]
theorem checked13567 : checkPrefixCuts (2^48) 1782185985 9 Manual.Count131072.C013567.packed 128 cuts13567 = true := by
 decide +kernel
def pointBounds13567 : List (Nat × Nat × Nat) := [(1782225920,94948227209443,94948604337993),(1782282240,94948640675316,94949017804158)]
theorem point_links_checked13567 : (cuts13567.take 2).map (fun c => (1782185985-1+2*2^9*c.k,94947936290899+c.lower,94948313419245+c.upper)) = pointBounds13567 := by
 decide +kernel
def cuts13568 : List PrefixCut := [⟨21,160452217,160452330⟩,
⟨76,574207760,574208169⟩,
⟨128,965052672,965053354⟩]
theorem checked13568 : checkPrefixCuts (2^48) 1782317057 9 Manual.Count131072.C013568.packed 128 cuts13568 = true := by
 decide +kernel
def pointBounds13568 : List (Nat × Nat × Nat) := [(1782338560,94949057128715,94949434257854),(1782394880,94949470884258,94949848013693)]
theorem point_links_checked13568 : (cuts13568.take 2).map (fun c => (1782317057-1+2*2^9*c.k,94948896676498+c.lower,94949273805524+c.upper)) = pointBounds13568 := by
 decide +kernel
def cuts13569 : List PrefixCut := [⟨3,23371365,23371382⟩,
⟨58,446891342,446891664⟩,
⟨113,866608219,866608834⟩,
⟨128,979351548,979352245⟩]
theorem checked13569 : checkPrefixCuts (2^48) 1782448129 9 Manual.Count131072.C013569.packed 128 cuts13569 = true := by
 decide +kernel
def pointBounds13569 : List (Nat × Nat × Nat) := [(1782451200,94949885100535,94950262230260),(1782507520,94950308620512,94950685750542),(1782563840,94950728337389,94951105467712)]
theorem point_links_checked13569 : (cuts13569.take 3).map (fun c => (1782448129-1+2*2^9*c.k,94949861729170+c.lower,94950238858878+c.upper)) = pointBounds13569 := by
 decide +kernel
def cuts13570 : List PrefixCut := [⟨40,300802118,300802330⟩,
⟨95,718597672,718598180⟩,
⟨128,971542302,971542994⟩]
theorem checked13570 : checkPrefixCuts (2^48) 1782579201 9 Manual.Count131072.C013570.packed 128 cuts13570 = true := by
 decide +kernel
def pointBounds13570 : List (Nat × Nat × Nat) := [(1782620160,94951141882836,94951519013453),(1782676480,94951559678390,94951936809303)]
theorem point_links_checked13570 : (cuts13570.take 2).map (fun c => (1782579201-1+2*2^9*c.k,94950841080718+c.lower,94951218211123+c.upper)) = pointBounds13570 := by
 decide +kernel
def cuts13571 : List PrefixCut := [⟨22,173837467,173837591⟩,
⟨77,589869878,589870296⟩,
⟨128,984575537,984576230⟩]
theorem checked13571 : checkPrefixCuts (2^48) 1782710273 9 Manual.Count131072.C013571.packed 128 cuts13571 = true := by
 decide +kernel
def pointBounds13571 : List (Nat × Nat × Nat) := [(1782732800,94951986460487,94952363591708),(1782789120,94952402492898,94952779624413)]
theorem point_links_checked13571 : (cuts13571.take 2).map (fun c => (1782710273-1+2*2^9*c.k,94951812623020+c.lower,94952189754117+c.upper)) = pointBounds13571 := by
 decide +kernel
def cuts13572 : List PrefixCut := [⟨4,31733831,31733852⟩,
⟨59,447424205,447424521⟩,
⟨114,872100204,872100818⟩,
⟨128,978503886,978504575⟩]
theorem checked13572 : checkPrefixCuts (2^48) 1782841345 9 Manual.Count131072.C013572.packed 128 cuts13572 = true := by
 decide +kernel
def pointBounds13572 : List (Nat × Nat × Nat) := [(1782845440,94952828932388,94953206064199),(1782901760,94953244622762,94953621754868),(1782958080,94953669298761,94954046431165)]
theorem point_links_checked13572 : (cuts13572.take 3).map (fun c => (1782841345-1+2*2^9*c.k,94952797198557+c.lower,94953174330347+c.upper)) = pointBounds13572 := by
 decide +kernel
def cuts13573 : List PrefixCut := [⟨41,306734567,306734784⟩,
⟨96,722385478,722385986⟩,
⟨128,966276365,966277046⟩]
theorem checked13573 : checkPrefixCuts (2^48) 1782972417 9 Manual.Count131072.C013573.packed 128 cuts13573 = true := by
 decide +kernel
def pointBounds13573 : List (Nat × Nat × Nat) := [(1783014400,94954082437010,94954459569706),(1783070720,94954498087921,94954875220908)]
theorem point_links_checked13573 : (cuts13573.take 2).map (fun c => (1782972417-1+2*2^9*c.k,94953775702443+c.lower,94954152834922+c.upper)) = pointBounds13573 := by
 decide +kernel
def cuts13574 : List PrefixCut := [⟨23,176009094,176009220⟩,
⟨78,591633864,591634285⟩,
⟨128,966363585,966364273⟩]
theorem checked13574 : checkPrefixCuts (2^48) 1783103489 9 Manual.Count131072.C013574.packed 128 cuts13574 = true := by
 decide +kernel
def pointBounds13574 : List (Nat × Nat × Nat) := [(1783127040,94954917987902,94955295121188),(1783183360,94955333612672,94955710746253)]
theorem point_links_checked13574 : (cuts13574.take 2).map (fun c => (1783103489-1+2*2^9*c.k,94954741978808+c.lower,94955119111968+c.upper)) = pointBounds13574 := by
 decide +kernel
def cuts13575 : List PrefixCut := [⟨5,38514155,38514183⟩,
⟨60,462162601,462162923⟩,
⟨115,879010620,879011236⟩,
⟨128,978130444,978131130⟩]
theorem checked13575 : checkPrefixCuts (2^48) 1783234561 9 Manual.Count131072.C013575.packed 128 cuts13575 = true := by
 decide +kernel
def pointBounds13575 : List (Nat × Nat × Nat) := [(1783239680,94955746856548,94956123990424),(1783296000,94956170504994,94956547639164),(1783352320,94956587353013,94956964487477)]
theorem point_links_checked13575 : (cuts13575.take 3).map (fun c => (1783234561-1+2*2^9*c.k,94955708342393+c.lower,94956085476241+c.upper)) = pointBounds13575 := by
 decide +kernel
def cuts13576 : List PrefixCut := [⟨42,315505392,315505616⟩,
⟨97,736588476,736588998⟩,
⟨128,972060859,972061549⟩]
theorem checked13576 : checkPrefixCuts (2^48) 1783365633 9 Manual.Count131072.C013576.packed 128 cuts13576 = true := by
 decide +kernel
def pointBounds13576 : List (Nat × Nat × Nat) := [(1783408640,94957001978229,94957379112987),(1783464960,94957423061313,94957800196369)]
theorem point_links_checked13576 : (cuts13576.take 2).map (fun c => (1783365633-1+2*2^9*c.k,94956686472837+c.lower,94957063607371+c.upper)) = pointBounds13576 := by
 decide +kernel
def cuts13577 : List PrefixCut := [⟨24,183861252,183861381⟩,
⟨79,592292309,592292727⟩,
⟨128,966939283,966939966⟩]
theorem checked13577 : checkPrefixCuts (2^48) 1783496705 9 Manual.Count131072.C013577.packed 128 cuts13577 = true := by
 decide +kernel
def pointBounds13577 : List (Nat × Nat × Nat) := [(1783521280,94957842394948,94958219530301),(1783577600,94958250826005,94958627961647)]
theorem point_links_checked13577 : (cuts13577.take 2).map (fun c => (1783496705-1+2*2^9*c.k,94957658533696+c.lower,94958035668920+c.upper)) = pointBounds13577 := by
 decide +kernel
def cuts13578 : List PrefixCut := [⟨6,47343015,47343046⟩,
⟨61,473264882,473265210⟩,
⟨116,889547309,889547937⟩,
⟨128,980124092,980124783⟩]
theorem checked13578 : checkPrefixCuts (2^48) 1783627777 9 Manual.Count131072.C013578.packed 128 cuts13578 = true := by
 decide +kernel
def pointBounds13578 : List (Nat × Nat × Nat) := [(1783633920,94958672815994,94959049951932),(1783690240,94959098737861,94959475874096),(1783746560,94959515020288,94959892156823)]
theorem point_links_checked13578 : (cuts13578.take 3).map (fun c => (1783627777-1+2*2^9*c.k,94958625472979+c.lower,94959002608886+c.upper)) = pointBounds13578 := by
 decide +kernel
def cuts13579 : List PrefixCut := [⟨43,325061419,325061647⟩,
⟨98,745104659,745105180⟩,
⟨128,965850789,965851468⟩]
theorem checked13579 : checkPrefixCuts (2^48) 1783758849 9 Manual.Count131072.C013579.packed 128 cuts13579 = true := by
 decide +kernel
def pointBounds13579 : List (Nat × Nat × Nat) := [(1783802880,94959930658490,94960307795316),(1783859200,94960350701730,94960727838849)]
theorem point_links_checked13579 : (cuts13579.take 2).map (fun c => (1783758849-1+2*2^9*c.k,94959605597071+c.lower,94959982733669+c.upper)) = pointBounds13579 := by
 decide +kernel
def cuts13580 : List PrefixCut := [⟨25,188238679,188238809⟩,
⟨80,599103957,599104373⟩,
⟨128,955681587,955682257⟩]
theorem checked13580 : checkPrefixCuts (2^48) 1783889921 9 Manual.Count131072.C013580.packed 128 cuts13580 = true := by
 decide +kernel
def pointBounds13580 : List (Nat × Nat × Nat) := [(1783915520,94960759686539,94961136823946),(1783971840,94961170551817,94961547689510)]
theorem point_links_checked13580 : (cuts13580.take 2).map (fun c => (1783889921-1+2*2^9*c.k,94960571447860+c.lower,94960948585137+c.upper)) = pointBounds13580 := by
 decide +kernel
def cuts13581 : List PrefixCut := [⟨7,53801351,53801390⟩,
⟨62,480733512,480733849⟩,
⟨117,895188607,895189237⟩,
⟨128,978803766,978804457⟩]
theorem checked13581 : checkPrefixCuts (2^48) 1784020993 9 Manual.Count131072.C013581.packed 128 cuts13581 = true := by
 decide +kernel
def pointBounds13581 : List (Nat × Nat × Nat) := [(1784028160,94961580930798,94961958068784),(1784084480,94962007862959,94962385001243),(1784140800,94962422318054,94962799456631)]
theorem point_links_checked13581 : (cuts13581.take 3).map (fun c => (1784020993-1+2*2^9*c.k,94961527129447+c.lower,94961904267394+c.upper)) = pointBounds13581 := by
 decide +kernel
def cuts13582 : List PrefixCut := [⟨44,333824287,333824523⟩,
⟨99,755509985,755510519⟩,
⟨128,971790268,971790952⟩]
theorem checked13582 : checkPrefixCuts (2^48) 1784152065 9 Manual.Count131072.C013582.packed 128 cuts13582 = true := by
 decide +kernel
def pointBounds13582 : List (Nat × Nat × Nat) := [(1784197120,94962839757500,94963216896374),(1784253440,94963261443198,94963638582370)]
theorem point_links_checked13582 : (cuts13582.take 2).map (fun c => (1784152065-1+2*2^9*c.k,94962505933213+c.lower,94962883071851+c.upper)) = pointBounds13582 := by
 decide +kernel
def cuts13583 : List PrefixCut := [⟨26,194507220,194507358⟩,
⟨81,603388735,603389165⟩,
⟨128,964777734,964778419⟩]
theorem checked13583 : checkPrefixCuts (2^48) 1784283137 9 Manual.Count131072.C013583.packed 128 cuts13583 = true := by
 decide +kernel
def pointBounds13583 : List (Nat × Nat × Nat) := [(1784309760,94963672230701,94964049370161),(1784366080,94964081112216,94964458251968)]
theorem point_links_checked13583 : (cuts13583.take 2).map (fun c => (1784283137-1+2*2^9*c.k,94963477723481+c.lower,94963854862803+c.upper)) = pointBounds13583 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000111
