import PlattAssemblyKernel
import PlattCertificates.Count131072.C014576
import PlattCertificates.Count131072.C014577
import PlattCertificates.Count131072.C014578
import PlattCertificates.Count131072.C014579
import PlattCertificates.Count131072.C014580
import PlattCertificates.Count131072.C014581
import PlattCertificates.Count131072.C014582
import PlattCertificates.Count131072.C014583
import PlattCertificates.Count131072.C014584
import PlattCertificates.Count131072.C014585
import PlattCertificates.Count131072.C014586
import PlattCertificates.Count131072.C014587
import PlattCertificates.Count131072.C014588
import PlattCertificates.Count131072.C014589
import PlattCertificates.Count131072.C014590
import PlattCertificates.Count131072.C014591
import PlattCertificates.Count131072.C014592
import PlattCertificates.Count131072.C014593
import PlattCertificates.Count131072.C014594
import PlattCertificates.Count131072.C014595
import PlattCertificates.Count131072.C014596
import PlattCertificates.Count131072.C014597
import PlattCertificates.Count131072.C014598
import PlattCertificates.Count131072.C014599
import PlattCertificates.Count131072.C014600
import PlattCertificates.Count131072.C014601
import PlattCertificates.Count131072.C014602
import PlattCertificates.Count131072.C014603
import PlattCertificates.Count131072.C014604
import PlattCertificates.Count131072.C014605
import PlattCertificates.Count131072.C014606
import PlattCertificates.Count131072.C014607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000143
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14576 : List PrefixCut := [⟨3,20142745,20142758⟩,
⟨62,442251161,442251462⟩,
⟨121,855819114,855819699⟩,
⟨128,906834245,906834863⟩]
theorem checked14576 : checkPrefixCuts (2^48) 1914437633 9 Manual.Count131072.C014576.packed 128 cuts14576 = true := by
 decide +kernel
def pointBounds14576 : List (Nat × Nat × Nat) := [(1914440704,95892187420757,95892565201946),(1914501120,95892609529173,95892987310650),(1914561536,95893023097126,95893400878887)]
theorem point_links_checked14576 : (cuts14576.take 3).map (fun c => (1914437633-1+2*2^9*c.k,95892167278012+c.lower,95892545059188+c.upper)) = pointBounds14576 := by
 decide +kernel
def cuts14577 : List PrefixCut := [⟨52,360187660,360187901⟩,
⟨111,781962181,781962705⟩,
⟨128,904419829,904420435⟩]
theorem checked14577 : checkPrefixCuts (2^48) 1914568705 9 Manual.Count131072.C014577.packed 128 cuts14577 = true := by
 decide +kernel
def pointBounds14577 : List (Nat × Nat × Nat) := [(1914621952,95893434299917,95893812081952),(1914682368,95893856074438,95894233856756)]
theorem point_links_checked14577 : (cuts14577.take 2).map (fun c => (1914568705-1+2*2^9*c.k,95893074112257+c.lower,95893451894051+c.upper)) = pointBounds14577 := by
 decide +kernel
def cuts14578 : List PrefixCut := [⟨42,295628359,295628560⟩,
⟨101,705910109,705910590⟩,
⟨128,898330901,898331512⟩]
theorem checked14578 : checkPrefixCuts (2^48) 1914699777 9 Manual.Count131072.C014578.packed 128 cuts14578 = true := by
 decide +kernel
def pointBounds14578 : List (Nat × Nat × Nat) := [(1914742784,95894274160445,95894651943046),(1914803200,95894684442195,95895062225076)]
theorem point_links_checked14578 : (cuts14578.take 2).map (fun c => (1914699777-1+2*2^9*c.k,95893978532086+c.lower,95894356314486+c.upper)) = pointBounds14578 := by
 decide +kernel
def cuts14579 : List PrefixCut := [⟨32,228431807,228431961⟩,
⟨91,641921487,641921917⟩,
⟨128,904884171,904884781⟩]
theorem checked14579 : checkPrefixCuts (2^48) 1914830849 9 Manual.Count131072.C014579.packed 128 cuts14579 = true := by
 decide +kernel
def pointBounds14579 : List (Nat × Nat × Nat) := [(1914863616,95895105294794,95895483077959),(1914924032,95895518784474,95895896567915)]
theorem point_links_checked14579 : (cuts14579.take 2).map (fun c => (1914830849-1+2*2^9*c.k,95894876862987+c.lower,95895254645998+c.upper)) = pointBounds14579 := by
 decide +kernel
def cuts14580 : List PrefixCut := [⟨22,152865783,152865888⟩,
⟨81,572061711,572062102⟩,
⟨128,906291941,906292557⟩]
theorem checked14580 : checkPrefixCuts (2^48) 1914961921 9 Manual.Count131072.C014580.packed 128 cuts14580 = true := by
 decide +kernel
def pointBounds14580 : List (Nat × Nat × Nat) := [(1914984448,95895934612941,95896312396667),(1915044864,95896353808869,95896731592881)]
theorem point_links_checked14580 : (cuts14580.take 2).map (fun c => (1914961921-1+2*2^9*c.k,95895781747158+c.lower,95896159530779+c.upper)) = pointBounds14580 := by
 decide +kernel
def cuts14581 : List PrefixCut := [⟨12,82453910,82453967⟩,
⟨71,503974946,503975289⟩,
⟨128,904613276,904613887⟩]
theorem checked14581 : checkPrefixCuts (2^48) 1915092993 9 Manual.Count131072.C014581.packed 128 cuts14581 = true := by
 decide +kernel
def pointBounds14581 : List (Nat × Nat × Nat) := [(1915105280,95896770493009,95897148277303),(1915165696,95897192014045,95897569798625)]
theorem point_links_checked14581 : (cuts14581.take 2).map (fun c => (1915092993-1+2*2^9*c.k,95896688039099+c.lower,95897065823336+c.upper)) = pointBounds14581 := by
 decide +kernel
def cuts14582 : List PrefixCut := [⟨2,13373997,13374006⟩,
⟨61,433251845,433252139⟩,
⟨120,853410304,853410883⟩,
⟨128,909401049,909401666⟩]
theorem checked14582 : checkPrefixCuts (2^48) 1915224065 9 Manual.Count131072.C014582.packed 128 cuts14582 = true := by
 decide +kernel
def pointBounds14582 : List (Nat × Nat × Nat) := [(1915226112,95897606026372,95897983811229),(1915286528,95898025904220,95898403689362),(1915346944,95898446062679,95898823848106)]
theorem point_links_checked14582 : (cuts14582.take 3).map (fun c => (1915224065-1+2*2^9*c.k,95897592652375+c.lower,95897970437223+c.upper)) = pointBounds14582 := by
 decide +kernel
def cuts14583 : List PrefixCut := [⟨51,357394610,357394854⟩,
⟨110,775763284,775763807⟩,
⟨128,899934067,899934673⟩]
theorem checked14583 : checkPrefixCuts (2^48) 1915355137 9 Manual.Count131072.C014583.packed 128 cuts14583 = true := by
 decide +kernel
def pointBounds14583 : List (Nat × Nat × Nat) := [(1915407360,95898859448034,95899237233743),(1915467776,95899277816708,95899655602696)]
theorem point_links_checked14583 : (cuts14583.take 2).map (fun c => (1915355137-1+2*2^9*c.k,95898502053424+c.lower,95898879838889+c.upper)) = pointBounds14583 := by
 decide +kernel
def cuts14584 : List PrefixCut := [⟨41,288600683,288600877⟩,
⟨100,704003979,704004456⟩,
⟨128,899431539,899432149⟩]
theorem checked14584 : checkPrefixCuts (2^48) 1915486209 9 Manual.Count131072.C014584.packed 128 cuts14584 = true := by
 decide +kernel
def pointBounds14584 : List (Nat × Nat × Nat) := [(1915528192,95899690588174,95900068374439),(1915588608,95900105991470,95900483778018)]
theorem point_links_checked14584 : (cuts14584.take 2).map (fun c => (1915486209-1+2*2^9*c.k,95899401987491+c.lower,95899779773562+c.upper)) = pointBounds14584 := by
 decide +kernel
def cuts14585 : List PrefixCut := [⟨31,220109657,220109804⟩,
⟨90,630197306,630197727⟩,
⟨128,896872246,896872846⟩]
theorem checked14585 : checkPrefixCuts (2^48) 1915617281 9 Manual.Count131072.C014585.packed 128 cuts14585 = true := by
 decide +kernel
def pointBounds14585 : List (Nat × Nat × Nat) := [(1915649024,95900521528687,95900899315515),(1915709440,95900931616336,95901309403438)]
theorem point_links_checked14585 : (cuts14585.take 2).map (fun c => (1915617281-1+2*2^9*c.k,95900301419030+c.lower,95900679205711+c.upper)) = pointBounds14585 := by
 decide +kernel
def cuts14586 : List PrefixCut := [⟨21,145897526,145897623⟩,
⟨80,564480804,564481186⟩,
⟨128,904891410,904892019⟩]
theorem checked14586 : checkPrefixCuts (2^48) 1915748353 9 Manual.Count131072.C014586.packed 128 cuts14586 = true := by
 decide +kernel
def pointBounds14586 : List (Nat × Nat × Nat) := [(1915769856,95901344188802,95901721976180),(1915830272,95901762772080,95902140559743)]
theorem point_links_checked14586 : (cuts14586.take 2).map (fun c => (1915748353-1+2*2^9*c.k,95901198291276+c.lower,95901576078557+c.upper)) = pointBounds14586 := by
 decide +kernel
def cuts14587 : List PrefixCut := [⟨11,76690349,76690400⟩,
⟨70,493190433,493190774⟩,
⟨128,902478881,902479499⟩]
theorem checked14587 : checkPrefixCuts (2^48) 1915879425 9 Manual.Count131072.C014587.packed 128 cuts14587 = true := by
 decide +kernel
def pointBounds14587 : List (Nat × Nat × Nat) := [(1915890688,95902179873035,95902557660976),(1915951104,95902596373119,95902974161350)]
theorem point_links_checked14587 : (cuts14587.take 2).map (fun c => (1915879425-1+2*2^9*c.k,95902103182686+c.lower,95902480970576+c.upper)) = pointBounds14587 := by
 decide +kernel
def cuts14588 : List PrefixCut := [⟨1,7051522,7051527⟩,
⟨60,424553706,424553991⟩,
⟨119,836019926,836020488⟩,
⟨128,900360841,900361445⟩]
theorem checked14588 : checkPrefixCuts (2^48) 1916010497 9 Manual.Count131072.C014588.packed 128 cuts14588 = true := by
 decide +kernel
def pointBounds14588 : List (Nat × Nat × Nat) := [(1916011520,95903012713089,95903390501602),(1916071936,95903430215273,95903808004066),(1916132352,95903841681493,95904219470563)]
theorem point_links_checked14588 : (cuts14588.take 3).map (fun c => (1916010497-1+2*2^9*c.k,95903005661567+c.lower,95903383450075+c.upper)) = pointBounds14588 := by
 decide +kernel
def cuts14589 : List PrefixCut := [⟨50,353869434,353869673⟩,
⟨109,765603317,765603834⟩,
⟨128,901033490,901034097⟩]
theorem checked14589 : checkPrefixCuts (2^48) 1916141569 9 Manual.Count131072.C014589.packed 128 cuts14589 = true := by
 decide +kernel
def pointBounds14589 : List (Nat × Nat × Nat) := [(1916192768,95904259891842,95904637681193),(1916253184,95904671625725,95905049415354)]
theorem point_links_checked14589 : (cuts14589.take 2).map (fun c => (1916141569-1+2*2^9*c.k,95903906022408+c.lower,95904283811520+c.upper)) = pointBounds14589 := by
 decide +kernel
def cuts14590 : List PrefixCut := [⟨40,281725555,281725747⟩,
⟨99,693580437,693580906⟩,
⟨128,892599784,892600390⟩]
theorem checked14590 : checkPrefixCuts (2^48) 1916272641 9 Manual.Count131072.C014590.packed 128 cuts14590 = true := by
 decide +kernel
def pointBounds14590 : List (Nat × Nat × Nat) := [(1916313600,95905088781453,95905466571364),(1916374016,95905500636335,95905878426523)]
theorem point_links_checked14590 : (cuts14590.take 2).map (fun c => (1916272641-1+2*2^9*c.k,95904807055898+c.lower,95905184845617+c.upper)) = pointBounds14590 := by
 decide +kernel
def cuts14591 : List PrefixCut := [⟨30,215466306,215466450⟩,
⟨89,620686000,620686423⟩,
⟨128,892098226,892098832⟩]
theorem checked14591 : checkPrefixCuts (2^48) 1916403713 9 Manual.Count131072.C014591.packed 128 cuts14591 = true := by
 decide +kernel
def pointBounds14591 : List (Nat × Nat × Nat) := [(1916434432,95905915121988,95906292912457),(1916494848,95906320341682,95906698132430)]
theorem point_links_checked14591 : (cuts14591.take 2).map (fun c => (1916403713-1+2*2^9*c.k,95905699655682+c.lower,95906077446007+c.upper)) = pointBounds14591 := by
 decide +kernel
def cuts14592 : List PrefixCut := [⟨20,139669372,139669468⟩,
⟨79,558374968,558375348⟩,
⟨128,908191770,908192385⟩]
theorem checked14592 : checkPrefixCuts (2^48) 1916534785 9 Manual.Count131072.C014592.packed 128 cuts14592 = true := by
 decide +kernel
def pointBounds14592 : List (Nat × Nat × Nat) := [(1916555264,95906731423280,95907109214307),(1916615680,95907150128876,95907527920187)]
theorem point_links_checked14592 : (cuts14592.take 2).map (fun c => (1916534785-1+2*2^9*c.k,95906591753908+c.lower,95906969544839+c.upper)) = pointBounds14592 := by
 decide +kernel
def cuts14593 : List PrefixCut := [⟨10,69756657,69756705⟩,
⟨69,485939135,485939462⟩,
⟨128,901521196,901521805⟩]
theorem checked14593 : checkPrefixCuts (2^48) 1916665857 9 Manual.Count131072.C014593.packed 128 cuts14593 = true := by
 decide +kernel
def pointBounds14593 : List (Nat × Nat × Nat) := [(1916676096,95907569702335,95907947493929),(1916736512,95907985884813,95908363676686),(1916796928,95908401466874,95908779259029)]
theorem point_links_checked14593 : (cuts14593.take 3).map (fun c => (1916665857-1+2*2^9*c.k,95907499945678+c.lower,95907877737224+c.upper)) = pointBounds14593 := by
 decide +kernel
def cuts14594 : List PrefixCut := [⟨59,403674644,403674919⟩,
⟨118,825544590,825545154⟩,
⟨128,896613613,896614223⟩]
theorem checked14594 : checkPrefixCuts (2^48) 1916796929 9 Manual.Count131072.C014594.packed 128 cuts14594 = true := by
 decide +kernel
def pointBounds14594 : List (Nat × Nat × Nat) := [(1916857344,95908805141518,95909182933948),(1916917760,95909227011464,95909604804183)]
theorem point_links_checked14594 : (cuts14594.take 2).map (fun c => (1916796929-1+2*2^9*c.k,95908401466874+c.lower,95908779259029+c.upper)) = pointBounds14594 := by
 decide +kernel
def cuts14595 : List PrefixCut := [⟨49,343152324,343152555⟩,
⟨108,756479586,756480098⟩,
⟨128,895965405,895966010⟩]
theorem checked14595 : checkPrefixCuts (2^48) 1916928001 9 Manual.Count131072.C014595.packed 128 cuts14595 = true := by
 decide +kernel
def pointBounds14595 : List (Nat × Nat × Nat) := [(1916978176,95909641232811,95910019025807),(1917038592,95910054560073,95910432353350)]
theorem point_links_checked14595 : (cuts14595.take 2).map (fun c => (1916928001-1+2*2^9*c.k,95909298080487+c.lower,95909675873252+c.upper)) = pointBounds14595 := by
 decide +kernel
def cuts14596 : List PrefixCut := [⟨39,270745082,270745267⟩,
⟨98,693002414,693002890⟩,
⟨128,898840580,898841193⟩]
theorem checked14596 : checkPrefixCuts (2^48) 1917059073 9 Manual.Count131072.C014596.packed 128 cuts14596 = true := by
 decide +kernel
def pointBounds14596 : List (Nat × Nat × Nat) := [(1917099008,95910464790974,95910842584529),(1917159424,95910887048306,95911264842152)]
theorem point_links_checked14596 : (cuts14596.take 2).map (fun c => (1917059073-1+2*2^9*c.k,95910194045892+c.lower,95910571839262+c.upper)) = pointBounds14596 := by
 decide +kernel
def cuts14597 : List PrefixCut := [⟨29,198641011,198641150⟩,
⟨88,612797042,612797462⟩,
⟨128,890410709,890411320⟩]
theorem checked14597 : checkPrefixCuts (2^48) 1917190145 9 Manual.Count131072.C014597.packed 128 cuts14597 = true := by
 decide +kernel
def pointBounds14597 : List (Nat × Nat × Nat) := [(1917219840,95911291527483,95911669321605),(1917280256,95911705683514,95912083477917)]
theorem point_links_checked14597 : (cuts14597.take 2).map (fun c => (1917190145-1+2*2^9*c.k,95911092886472+c.lower,95911470680455+c.upper)) = pointBounds14597 := by
 decide +kernel
def cuts14598 : List PrefixCut := [⟨19,136088772,136088863⟩,
⟨78,553741924,553742296⟩,
⟨128,908112880,908113486⟩]
theorem checked14598 : checkPrefixCuts (2^48) 1917321217 9 Manual.Count131072.C014598.packed 128 cuts14598 = true := by
 decide +kernel
def pointBounds14598 : List (Nat × Nat × Nat) := [(1917340672,95912119385953,95912497180638),(1917401088,95912537039105,95912914834071)]
theorem point_links_checked14598 : (cuts14598.take 2).map (fun c => (1917321217-1+2*2^9*c.k,95911983297181+c.lower,95912361091775+c.upper)) = pointBounds14598 := by
 decide +kernel
def cuts14599 : List PrefixCut := [⟨9,62681860,62681900⟩,
⟨68,480161890,480162211⟩,
⟨127,889408632,889409230⟩,
⟨128,896747947,896748550⟩]
theorem checked14599 : checkPrefixCuts (2^48) 1917452289 9 Manual.Count131072.C014599.packed 128 cuts14599 = true := by
 decide +kernel
def pointBounds14599 : List (Nat × Nat × Nat) := [(1917461504,95912954091921,95913331887161),(1917521920,95913371571951,95913749367472),(1917582336,95913780818693,95914158614491)]
theorem point_links_checked14599 : (cuts14599.take 3).map (fun c => (1917452289-1+2*2^9*c.k,95912891410061+c.lower,95913269205261+c.upper)) = pointBounds14599 := by
 decide +kernel
def cuts14600 : List PrefixCut := [⟨58,406298115,406298391⟩,
⟨117,822564532,822565085⟩,
⟨128,896393185,896393788⟩]
theorem checked14600 : checkPrefixCuts (2^48) 1917583361 9 Manual.Count131072.C014600.packed 128 cuts14600 = true := by
 decide +kernel
def pointBounds14600 : List (Nat × Nat × Nat) := [(1917642752,95914194456123,95914572252202),(1917703168,95914610722540,95914988518896)]
theorem point_links_checked14600 : (cuts14600.take 2).map (fun c => (1917583361-1+2*2^9*c.k,95913788158008+c.lower,95914165953811+c.upper)) = pointBounds14600 := by
 decide +kernel
def cuts14601 : List PrefixCut := [⟨48,339048751,339048976⟩,
⟨107,751326234,751326737⟩,
⟨128,901762414,901763017⟩]
theorem checked14601 : checkPrefixCuts (2^48) 1917714433 9 Manual.Count131072.C014601.packed 128 cuts14601 = true := by
 decide +kernel
def pointBounds14601 : List (Nat × Nat × Nat) := [(1917763584,95915023599944,95915401396575),(1917824000,95915435877427,95915813674336)]
theorem point_links_checked14601 : (cuts14601.take 2).map (fun c => (1917714433-1+2*2^9*c.k,95914684551193+c.lower,95915062347599+c.upper)) = pointBounds14601 := by
 decide +kernel
def cuts14602 : List PrefixCut := [⟨38,260654089,260654267⟩,
⟨97,684206022,684206483⟩,
⟨128,897150942,897151549⟩]
theorem checked14602 : checkPrefixCuts (2^48) 1917845505 9 Manual.Count131072.C014602.packed 128 cuts14602 = true := by
 decide +kernel
def pointBounds14602 : List (Nat × Nat × Nat) := [(1917884416,95915846967696,95916224764883),(1917944832,95916270519629,95916648317099)]
theorem point_links_checked14602 : (cuts14602.take 2).map (fun c => (1917845505-1+2*2^9*c.k,95915586313607+c.lower,95915964110616+c.upper)) = pointBounds14602 := by
 decide +kernel
def cuts14603 : List PrefixCut := [⟨28,193129688,193129823⟩,
⟨87,603153830,603154247⟩,
⟨128,889165170,889165780⟩]
theorem checked14603 : checkPrefixCuts (2^48) 1917976577 9 Manual.Count131072.C014603.packed 128 cuts14603 = true := by
 decide +kernel
def pointBounds14603 : List (Nat × Nat × Nat) := [(1918005248,95916676594237,95917054391988),(1918065664,95917086618379,95917464416412)]
theorem point_links_checked14603 : (cuts14603.take 2).map (fun c => (1917976577-1+2*2^9*c.k,95916483464549+c.lower,95916861262165+c.upper)) = pointBounds14603 := by
 decide +kernel
def cuts14604 : List PrefixCut := [⟨18,121211734,121211817⟩,
⟨77,536933037,536933399⟩,
⟨128,894093561,894094160⟩]
theorem checked14604 : checkPrefixCuts (2^48) 1918107649 9 Manual.Count131072.C014604.packed 128 cuts14604 = true := by
 decide +kernel
def pointBounds14604 : List (Nat × Nat × Nat) := [(1918126080,95917493841453,95917871639762),(1918186496,95917909562756,95918287361344)]
theorem point_links_checked14604 : (cuts14604.take 2).map (fun c => (1918107649-1+2*2^9*c.k,95917372629719+c.lower,95917750427945+c.upper)) = pointBounds14604 := by
 decide +kernel
def cuts14605 : List PrefixCut := [⟨8,54879187,54879224⟩,
⟨67,473655673,473655990⟩,
⟨126,882441414,882442009⟩,
⟨128,898581292,898581897⟩]
theorem checked14605 : checkPrefixCuts (2^48) 1918238721 9 Manual.Count131072.C014605.packed 128 cuts14605 = true := by
 decide +kernel
def pointBounds14605 : List (Nat × Nat × Nat) := [(1918246912,95918321602467,95918699401329),(1918307328,95918740378953,95919118178095),(1918367744,95919149164694,95919526964114)]
theorem point_links_checked14605 : (cuts14605.take 3).map (fun c => (1918238721-1+2*2^9*c.k,95918266723280+c.lower,95918644522105+c.upper)) = pointBounds14605 := by
 decide +kernel
def cuts14606 : List PrefixCut := [⟨57,389405096,389405361⟩,
⟨116,802273175,802273720⟩,
⟨128,884581138,884581739⟩]
theorem checked14606 : checkPrefixCuts (2^48) 1918369793 9 Manual.Count131072.C014606.packed 128 cuts14606 = true := by
 decide +kernel
def pointBounds14606 : List (Nat × Nat × Nat) := [(1918428160,95919554709668,95919932509363),(1918488576,95919967577747,95920345377722)]
theorem point_links_checked14606 : (cuts14606.take 2).map (fun c => (1918369793-1+2*2^9*c.k,95919165304572+c.lower,95919543104002+c.upper)) = pointBounds14606 := by
 decide +kernel
def cuts14607 : List PrefixCut := [⟨47,335388714,335388943⟩,
⟨106,747350590,747351099⟩,
⟨128,904767075,904767686⟩]
theorem checked14607 : checkPrefixCuts (2^48) 1918500865 9 Manual.Count131072.C014607.packed 128 cuts14607 = true := by
 decide +kernel
def pointBounds14607 : List (Nat × Nat × Nat) := [(1918548992,95920385274424,95920763074684),(1918609408,95920797236300,95921175036840)]
theorem point_links_checked14607 : (cuts14607.take 2).map (fun c => (1918500865-1+2*2^9*c.k,95920049885710+c.lower,95920427685741+c.upper)) = pointBounds14607 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000143
