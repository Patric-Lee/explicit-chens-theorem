import PlattAssemblyKernel
import PlattCertificates.Count131072.C039600
import PlattCertificates.Count131072.C039601
import PlattCertificates.Count131072.C039602
import PlattCertificates.Count131072.C039603
import PlattCertificates.Count131072.C039604
import PlattCertificates.Count131072.C039605
import PlattCertificates.Count131072.C039606
import PlattCertificates.Count131072.C039607
import PlattCertificates.Count131072.C039608
import PlattCertificates.Count131072.C039609
import PlattCertificates.Count131072.C039610
import PlattCertificates.Count131072.C039611
import PlattCertificates.Count131072.C039612
import PlattCertificates.Count131072.C039613
import PlattCertificates.Count131072.C039614
import PlattCertificates.Count131072.C039615
import PlattCertificates.Count131072.C039616
import PlattCertificates.Count131072.C039617
import PlattCertificates.Count131072.C039618
import PlattCertificates.Count131072.C039619
import PlattCertificates.Count131072.C039620
import PlattCertificates.Count131072.C039621
import PlattCertificates.Count131072.C039622
import PlattCertificates.Count131072.C039623
import PlattCertificates.Count131072.C039624
import PlattCertificates.Count131072.C039625
import PlattCertificates.Count131072.C039626
import PlattCertificates.Count131072.C039627
import PlattCertificates.Count131072.C039628
import PlattCertificates.Count131072.C039629
import PlattCertificates.Count131072.C039630
import PlattCertificates.Count131072.C039631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000300
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39600 : List PrefixCut := [⟨4,19020084,19020096⟩,
⟨64,321224304,321224498⟩]
theorem checked39600 : checkPrefixCuts (2^48) 5194383361 10 Manual.Count131072.C039600.packed 64 cuts39600 = true := by
 decide +kernel
def pointBounds39600 : List (Nat × Nat × Nat) := [(5194391552,108739907686495,108740293117023)]
theorem point_links_checked39600 : (cuts39600.take 1).map (fun c => (5194383361-1+2*2^10*c.k,108739888666411+c.lower,108740274096927+c.upper)) = pointBounds39600 := by
 decide +kernel
def cuts39601 : List PrefixCut := [⟨20,101004077,101004135⟩,
⟨64,321487140,321487328⟩]
theorem checked39601 : checkPrefixCuts (2^48) 5194514433 10 Manual.Count131072.C039601.packed 64 cuts39601 = true := by
 decide +kernel
def pointBounds39601 : List (Nat × Nat × Nat) := [(5194555392,108740310894792,108740696325560)]
theorem point_links_checked39601 : (cuts39601.take 1).map (fun c => (5194514433-1+2*2^10*c.k,108740209890715+c.lower,108740595321425+c.upper)) = pointBounds39601 := by
 decide +kernel
def cuts39602 : List PrefixCut := [⟨36,179515581,179515689⟩,
⟨64,317469352,317469545⟩]
theorem checked39602 : checkPrefixCuts (2^48) 5194645505 10 Manual.Count131072.C039602.packed 64 cuts39602 = true := by
 decide +kernel
def pointBounds39602 : List (Nat × Nat × Nat) := [(5194719232,108740710893436,108741096324442)]
theorem point_links_checked39602 : (cuts39602.take 1).map (fun c => (5194645505-1+2*2^10*c.k,108740531377855+c.lower,108740916808753+c.upper)) = pointBounds39602 := by
 decide +kernel
def cuts39603 : List PrefixCut := [⟨52,257426587,257426743⟩,
⟨64,317190410,317190602⟩]
theorem checked39603 : checkPrefixCuts (2^48) 5194776577 10 Manual.Count131072.C039603.packed 64 cuts39603 = true := by
 decide +kernel
def pointBounds39603 : List (Nat × Nat × Nat) := [(5194883072,108741106273794,108741491705041)]
theorem point_links_checked39603 : (cuts39603.take 1).map (fun c => (5194776577-1+2*2^10*c.k,108740848847207+c.lower,108741234278298+c.upper)) = pointBounds39603 := by
 decide +kernel
def cuts39604 : List PrefixCut := [⟨64,322708995,322709182⟩]
theorem checked39604 : checkPrefixCuts (2^48) 5194907649 10 Manual.Count131072.C039604.packed 64 cuts39604 = true := by
 decide +kernel
def cuts39605 : List PrefixCut := [⟨4,19180229,19180240⟩,
⟨64,318095428,318095617⟩]
theorem checked39605 : checkPrefixCuts (2^48) 5195038721 10 Manual.Count131072.C039605.packed 64 cuts39605 = true := by
 decide +kernel
def pointBounds39605 : List (Nat × Nat × Nat) := [(5195046912,108741507926841,108741893358322)]
theorem point_links_checked39605 : (cuts39605.take 1).map (fun c => (5195038721-1+2*2^10*c.k,108741488746612+c.lower,108741874178082+c.upper)) = pointBounds39605 := by
 decide +kernel
def cuts39606 : List PrefixCut := [⟨20,97523824,97523883⟩,
⟨64,317437248,317437436⟩]
theorem checked39606 : checkPrefixCuts (2^48) 5195169793 10 Manual.Count131072.C039606.packed 64 cuts39606 = true := by
 decide +kernel
def pointBounds39606 : List (Nat × Nat × Nat) := [(5195210752,108741904365864,108742289797582)]
theorem point_links_checked39606 : (cuts39606.take 1).map (fun c => (5195169793-1+2*2^10*c.k,108741806842040+c.lower,108742192273699+c.upper)) = pointBounds39606 := by
 decide +kernel
def cuts39607 : List PrefixCut := [⟨36,179276209,179276316⟩,
⟨64,317483472,317483660⟩]
theorem checked39607 : checkPrefixCuts (2^48) 5195300865 10 Manual.Count131072.C039607.packed 64 cuts39607 = true := by
 decide +kernel
def pointBounds39607 : List (Nat × Nat × Nat) := [(5195374592,108742303555497,108742688987451)]
theorem point_links_checked39607 : (cuts39607.take 1).map (fun c => (5195300865-1+2*2^10*c.k,108742124279288+c.lower,108742509711135+c.upper)) = pointBounds39607 := by
 decide +kernel
def cuts39608 : List PrefixCut := [⟨52,255768783,255768935⟩,
⟨64,317312878,317313066⟩]
theorem checked39608 : checkPrefixCuts (2^48) 5195431937 10 Manual.Count131072.C039608.packed 64 cuts39608 = true := by
 decide +kernel
def pointBounds39608 : List (Nat × Nat × Nat) := [(5195538432,108742697531543,108743082963730)]
theorem point_links_checked39608 : (cuts39608.take 1).map (fun c => (5195431937-1+2*2^10*c.k,108742441762760+c.lower,108742827194795+c.upper)) = pointBounds39608 := by
 decide +kernel
def cuts39609 : List PrefixCut := [⟨64,321313868,321314055⟩]
theorem checked39609 : checkPrefixCuts (2^48) 5195563009 10 Manual.Count131072.C039609.packed 64 cuts39609 = true := by
 decide +kernel
def cuts39610 : List PrefixCut := [⟨4,20423826,20423839⟩,
⟨64,316375982,316376170⟩]
theorem checked39610 : checkPrefixCuts (2^48) 5195694081 10 Manual.Count131072.C039610.packed 64 cuts39610 = true := by
 decide +kernel
def pointBounds39610 : List (Nat × Nat × Nat) := [(5195702272,108743100813332,108743486245755)]
theorem point_links_checked39610 : (cuts39610.take 1).map (fun c => (5195694081-1+2*2^10*c.k,108743080389506+c.lower,108743465821916+c.upper)) = pointBounds39610 := by
 decide +kernel
def cuts39611 : List PrefixCut := [⟨20,99786793,99786853⟩,
⟨64,316367978,316368167⟩]
theorem checked39611 : checkPrefixCuts (2^48) 5195825153 10 Manual.Count131072.C039611.packed 64 cuts39611 = true := by
 decide +kernel
def pointBounds39611 : List (Nat × Nat × Nat) := [(5195866112,108743496552281,108743881984939)]
theorem point_links_checked39611 : (cuts39611.take 1).map (fun c => (5195825153-1+2*2^10*c.k,108743396765488+c.lower,108743782198086+c.upper)) = pointBounds39611 := by
 decide +kernel
def cuts39612 : List PrefixCut := [⟨36,180337016,180337123⟩,
⟨64,318960210,318960397⟩]
theorem checked39612 : checkPrefixCuts (2^48) 5195956225 10 Manual.Count131072.C039612.packed 64 cuts39612 = true := by
 decide +kernel
def pointBounds39612 : List (Nat × Nat × Nat) := [(5196029952,108743893470482,108744278903376)]
theorem point_links_checked39612 : (cuts39612.take 1).map (fun c => (5195956225-1+2*2^10*c.k,108743713133466+c.lower,108744098566253+c.upper)) = pointBounds39612 := by
 decide +kernel
def cuts39613 : List PrefixCut := [⟨52,260340974,260341129⟩,
⟨64,318247965,318248155⟩]
theorem checked39613 : checkPrefixCuts (2^48) 5196087297 10 Manual.Count131072.C039613.packed 64 cuts39613 = true := by
 decide +kernel
def pointBounds39613 : List (Nat × Nat × Nat) := [(5196193792,108744292434650,108744677867779)]
theorem point_links_checked39613 : (cuts39613.take 1).map (fun c => (5196087297-1+2*2^10*c.k,108744032093676+c.lower,108744417526650+c.upper)) = pointBounds39613 := by
 decide +kernel
def cuts39614 : List PrefixCut := [⟨64,315043994,315044185⟩]
theorem checked39614 : checkPrefixCuts (2^48) 5196218369 10 Manual.Count131072.C039614.packed 64 cuts39614 = true := by
 decide +kernel
def cuts39615 : List PrefixCut := [⟨4,19392062,19392074⟩,
⟨64,317202675,317202862⟩]
theorem checked39615 : checkPrefixCuts (2^48) 5196349441 10 Manual.Count131072.C039615.packed 64 cuts39615 = true := by
 decide +kernel
def pointBounds39615 : List (Nat × Nat × Nat) := [(5196357632,108744684777697,108745070211064)]
theorem point_links_checked39615 : (cuts39615.take 1).map (fun c => (5196349441-1+2*2^10*c.k,108744665385635+c.lower,108745050818990+c.upper)) = pointBounds39615 := by
 decide +kernel
def cuts39616 : List PrefixCut := [⟨20,97607555,97607613⟩,
⟨64,312157345,312157531⟩]
theorem checked39616 : checkPrefixCuts (2^48) 5196480513 10 Manual.Count131072.C039616.packed 64 cuts39616 = true := by
 decide +kernel
def pointBounds39616 : List (Nat × Nat × Nat) := [(5196521472,108745080195865,108745465629465)]
theorem point_links_checked39616 : (cuts39616.take 1).map (fun c => (5196480513-1+2*2^10*c.k,108744982588310+c.lower,108745368021852+c.upper)) = pointBounds39616 := by
 decide +kernel
def cuts39617 : List PrefixCut := [⟨36,177931050,177931156⟩,
⟨64,316807586,316807776⟩]
theorem checked39617 : checkPrefixCuts (2^48) 5196611585 10 Manual.Count131072.C039617.packed 64 cuts39617 = true := by
 decide +kernel
def pointBounds39617 : List (Nat × Nat × Nat) := [(5196685312,108745472676705,108745858110539)]
theorem point_links_checked39617 : (cuts39617.take 1).map (fun c => (5196611585-1+2*2^10*c.k,108745294745655+c.lower,108745680179383+c.upper)) = pointBounds39617 := by
 decide +kernel
def cuts39618 : List PrefixCut := [⟨52,258629107,258629258⟩,
⟨64,317449558,317449744⟩]
theorem checked39618 : checkPrefixCuts (2^48) 5196742657 10 Manual.Count131072.C039618.packed 64 cuts39618 = true := by
 decide +kernel
def pointBounds39618 : List (Nat × Nat × Nat) := [(5196849152,108745870182348,108746255616417)]
theorem point_links_checked39618 : (cuts39618.take 1).map (fun c => (5196742657-1+2*2^10*c.k,108745611553241+c.lower,108745996987159+c.upper)) = pointBounds39618 := by
 decide +kernel
def cuts39619 : List PrefixCut := [⟨64,316683271,316683457⟩]
theorem checked39619 : checkPrefixCuts (2^48) 5196873729 10 Manual.Count131072.C039619.packed 64 cuts39619 = true := by
 decide +kernel
def cuts39620 : List PrefixCut := [⟨4,19931226,19931237⟩,
⟨64,316133683,316133872⟩]
theorem checked39620 : checkPrefixCuts (2^48) 5197004801 10 Manual.Count131072.C039620.packed 64 cuts39620 = true := by
 decide +kernel
def pointBounds39620 : List (Nat × Nat × Nat) := [(5197012992,108746265617296,108746651051597)]
theorem point_links_checked39620 : (cuts39620.take 1).map (fun c => (5197004801-1+2*2^10*c.k,108746245686070+c.lower,108746631120360+c.upper)) = pointBounds39620 := by
 decide +kernel
def cuts39621 : List PrefixCut := [⟨20,99924093,99924151⟩,
⟨64,317967108,317967296⟩]
theorem checked39621 : checkPrefixCuts (2^48) 5197135873 10 Manual.Count131072.C039621.packed 64 cuts39621 = true := by
 decide +kernel
def pointBounds39621 : List (Nat × Nat × Nat) := [(5197176832,108746661743846,108747047178383)]
theorem point_links_checked39621 : (cuts39621.take 1).map (fun c => (5197135873-1+2*2^10*c.k,108746561819753+c.lower,108746947254232+c.upper)) = pointBounds39621 := by
 decide +kernel
def cuts39622 : List PrefixCut := [⟨36,178666813,178666920⟩,
⟨64,319475498,319475689⟩]
theorem checked39622 : checkPrefixCuts (2^48) 5197266945 10 Manual.Count131072.C039622.packed 64 cuts39622 = true := by
 decide +kernel
def pointBounds39622 : List (Nat × Nat × Nat) := [(5197340672,108747058453674,108747443888448)]
theorem point_links_checked39622 : (cuts39622.take 1).map (fun c => (5197266945-1+2*2^10*c.k,108746879786861+c.lower,108747265221528+c.upper)) = pointBounds39622 := by
 decide +kernel
def cuts39623 : List PrefixCut := [⟨52,259842048,259842205⟩,
⟨64,320388062,320388254⟩]
theorem checked39623 : checkPrefixCuts (2^48) 5197398017 10 Manual.Count131072.C039623.packed 64 cuts39623 = true := by
 decide +kernel
def pointBounds39623 : List (Nat × Nat × Nat) := [(5197504512,108747459104407,108747844539422)]
theorem point_links_checked39623 : (cuts39623.take 1).map (fun c => (5197398017-1+2*2^10*c.k,108747199262359+c.lower,108747584697217+c.upper)) = pointBounds39623 := by
 decide +kernel
def cuts39624 : List PrefixCut := [⟨64,315993472,315993658⟩]
theorem checked39624 : checkPrefixCuts (2^48) 5197529089 10 Manual.Count131072.C039624.packed 64 cuts39624 = true := by
 decide +kernel
def cuts39625 : List PrefixCut := [⟨4,20632717,20632729⟩,
⟨64,315768940,315769128⟩]
theorem checked39625 : checkPrefixCuts (2^48) 5197660161 10 Manual.Count131072.C039625.packed 64 cuts39625 = true := by
 decide +kernel
def pointBounds39625 : List (Nat × Nat × Nat) := [(5197668352,108747856276610,108748241711858)]
theorem point_links_checked39625 : (cuts39625.take 1).map (fun c => (5197660161-1+2*2^10*c.k,108747835643893+c.lower,108748221079129+c.upper)) = pointBounds39625 := by
 decide +kernel
def cuts39626 : List PrefixCut := [⟨20,98449382,98449441⟩,
⟨64,315056947,315057135⟩]
theorem checked39626 : checkPrefixCuts (2^48) 5197791233 10 Manual.Count131072.C039626.packed 64 cuts39626 = true := by
 decide +kernel
def pointBounds39626 : List (Nat × Nat × Nat) := [(5197832192,108748249862215,108748635297698)]
theorem point_links_checked39626 : (cuts39626.take 1).map (fun c => (5197791233-1+2*2^10*c.k,108748151412833+c.lower,108748536848257+c.upper)) = pointBounds39626 := by
 decide +kernel
def cuts39627 : List PrefixCut := [⟨36,181839201,181839307⟩,
⟨64,320843156,320843348⟩]
theorem checked39627 : checkPrefixCuts (2^48) 5197922305 10 Manual.Count131072.C039627.packed 64 cuts39627 = true := by
 decide +kernel
def pointBounds39627 : List (Nat × Nat × Nat) := [(5197996032,108748648308981,108749033744699)]
theorem point_links_checked39627 : (cuts39627.take 1).map (fun c => (5197922305-1+2*2^10*c.k,108748466469780+c.lower,108748851905392+c.upper)) = pointBounds39627 := by
 decide +kernel
def cuts39628 : List PrefixCut := [⟨52,254340241,254340393⟩,
⟨64,314824469,314824656⟩]
theorem checked39628 : checkPrefixCuts (2^48) 5198053377 10 Manual.Count131072.C039628.packed 64 cuts39628 = true := by
 decide +kernel
def pointBounds39628 : List (Nat × Nat × Nat) := [(5198159872,108749041653177,108749427089133)]
theorem point_links_checked39628 : (cuts39628.take 1).map (fun c => (5198053377-1+2*2^10*c.k,108748787312936+c.lower,108749172748740+c.upper)) = pointBounds39628 := by
 decide +kernel
def cuts39629 : List PrefixCut := [⟨64,314924817,314925008⟩]
theorem checked39629 : checkPrefixCuts (2^48) 5198184449 10 Manual.Count131072.C039629.packed 64 cuts39629 = true := by
 decide +kernel
def cuts39630 : List PrefixCut := [⟨4,18518370,18518382⟩,
⟨64,319573475,319573664⟩]
theorem checked39630 : checkPrefixCuts (2^48) 5198315521 10 Manual.Count131072.C039630.packed 64 cuts39630 = true := by
 decide +kernel
def pointBounds39630 : List (Nat × Nat × Nat) := [(5198323712,108749435580592,108749821016786)]
theorem point_links_checked39630 : (cuts39630.take 1).map (fun c => (5198315521-1+2*2^10*c.k,108749417062222+c.lower,108749802498404+c.upper)) = pointBounds39630 := by
 decide +kernel
def cuts39631 : List PrefixCut := [⟨20,99303303,99303359⟩,
⟨64,311660247,311660430⟩]
theorem checked39631 : checkPrefixCuts (2^48) 5198446593 10 Manual.Count131072.C039631.packed 64 cuts39631 = true := by
 decide +kernel
def pointBounds39631 : List (Nat × Nat × Nat) := [(5198487552,108749835939000,108750221375427)]
theorem point_links_checked39631 : (cuts39631.take 1).map (fun c => (5198446593-1+2*2^10*c.k,108749736635697+c.lower,108750122072068+c.upper)) = pointBounds39631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000300
