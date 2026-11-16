import PlattAssemblyKernel
import PlattCertificates.Count131072.C072592
import PlattCertificates.Count131072.C072593
import PlattCertificates.Count131072.C072594
import PlattCertificates.Count131072.C072595
import PlattCertificates.Count131072.C072596
import PlattCertificates.Count131072.C072597
import PlattCertificates.Count131072.C072598
import PlattCertificates.Count131072.C072599
import PlattCertificates.Count131072.C072600
import PlattCertificates.Count131072.C072601
import PlattCertificates.Count131072.C072602
import PlattCertificates.Count131072.C072603
import PlattCertificates.Count131072.C072604
import PlattCertificates.Count131072.C072605
import PlattCertificates.Count131072.C072606
import PlattCertificates.Count131072.C072607
import PlattCertificates.Count131072.C072608
import PlattCertificates.Count131072.C072609
import PlattCertificates.Count131072.C072610
import PlattCertificates.Count131072.C072611
import PlattCertificates.Count131072.C072612
import PlattCertificates.Count131072.C072613
import PlattCertificates.Count131072.C072614
import PlattCertificates.Count131072.C072615
import PlattCertificates.Count131072.C072616
import PlattCertificates.Count131072.C072617
import PlattCertificates.Count131072.C072618
import PlattCertificates.Count131072.C072619
import PlattCertificates.Count131072.C072620
import PlattCertificates.Count131072.C072621
import PlattCertificates.Count131072.C072622
import PlattCertificates.Count131072.C072623
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72592 : List PrefixCut := [⟨64,166097448,166097549⟩]
theorem checked72592 : checkPrefixCuts (2^48) 9518710785 10 Manual.Count131072.C072592.packed 64 cuts72592 = true := by
 decide +kernel
def cuts72593 : List PrefixCut := [⟨64,171329073,171329171⟩]
theorem checked72593 : checkPrefixCuts (2^48) 9518841857 10 Manual.Count131072.C072593.packed 64 cuts72593 = true := by
 decide +kernel
def cuts72594 : List PrefixCut := [⟨6,15701597,15701607⟩,
⟨64,171178871,171178968⟩]
theorem checked72594 : checkPrefixCuts (2^48) 9518972929 10 Manual.Count131072.C072594.packed 64 cuts72594 = true := by
 decide +kernel
def pointBounds72594 : List (Nat × Nat × Nat) := [(9518985216,116259684475084,116260074244040)]
theorem point_links_checked72594 : (cuts72594.take 1).map (fun c => (9518972929-1+2*2^10*c.k,116259668773487+c.lower,116260058542433+c.upper)) = pointBounds72594 := by
 decide +kernel
def cuts72595 : List PrefixCut := [⟨64,168042150,168042254⟩]
theorem checked72595 : checkPrefixCuts (2^48) 9519104001 10 Manual.Count131072.C072595.packed 64 cuts72595 = true := by
 decide +kernel
def cuts72596 : List PrefixCut := [⟨24,64460399,64460433⟩,
⟨64,169459158,169459259⟩]
theorem checked72596 : checkPrefixCuts (2^48) 9519235073 10 Manual.Count131072.C072596.packed 64 cuts72596 = true := by
 decide +kernel
def pointBounds72596 : List (Nat × Nat × Nat) := [(9519284224,116260072454907,116260462224088)]
theorem point_links_checked72596 : (cuts72596.take 1).map (fun c => (9519235073-1+2*2^10*c.k,116260007994508+c.lower,116260397763655+c.upper)) = pointBounds72596 := by
 decide +kernel
def cuts72597 : List PrefixCut := [⟨64,169427252,169427351⟩]
theorem checked72597 : checkPrefixCuts (2^48) 9519366145 10 Manual.Count131072.C072597.packed 64 cuts72597 = true := by
 decide +kernel
def cuts72598 : List PrefixCut := [⟨42,109875125,109875193⟩,
⟨64,168390030,168390129⟩]
theorem checked72598 : checkPrefixCuts (2^48) 9519497217 10 Manual.Count131072.C072598.packed 64 cuts72598 = true := by
 decide +kernel
def pointBounds72598 : List (Nat × Nat × Nat) := [(9519583232,116260456756043,116260846525458)]
theorem point_links_checked72598 : (cuts72598.take 1).map (fun c => (9519497217-1+2*2^10*c.k,116260346880918+c.lower,116260736650265+c.upper)) = pointBounds72598 := by
 decide +kernel
def cuts72599 : List PrefixCut := [⟨64,168299003,168299098⟩]
theorem checked72599 : checkPrefixCuts (2^48) 9519628289 10 Manual.Count131072.C072599.packed 64 cuts72599 = true := by
 decide +kernel
def cuts72600 : List PrefixCut := [⟨60,159633573,159633666⟩,
⟨64,170248143,170248240⟩]
theorem checked72600 : checkPrefixCuts (2^48) 9519759361 10 Manual.Count131072.C072600.packed 64 cuts72600 = true := by
 decide +kernel
def pointBounds72600 : List (Nat × Nat × Nat) := [(9519882240,116260843203524,116261232973158)]
theorem point_links_checked72600 : (cuts72600.take 1).map (fun c => (9519759361-1+2*2^10*c.k,116260683569951+c.lower,116261073339492+c.upper)) = pointBounds72600 := by
 decide +kernel
def cuts72601 : List PrefixCut := [⟨64,168146552,168146653⟩]
theorem checked72601 : checkPrefixCuts (2^48) 9519890433 10 Manual.Count131072.C072601.packed 64 cuts72601 = true := by
 decide +kernel
def cuts72602 : List PrefixCut := [⟨64,166133702,166133802⟩]
theorem checked72602 : checkPrefixCuts (2^48) 9520021505 10 Manual.Count131072.C072602.packed 64 cuts72602 = true := by
 decide +kernel
def cuts72603 : List PrefixCut := [⟨14,38110797,38110817⟩,
⟨64,169590651,169590749⟩]
theorem checked72603 : checkPrefixCuts (2^48) 9520152577 10 Manual.Count131072.C072603.packed 64 cuts72603 = true := by
 decide +kernel
def pointBounds72603 : List (Nat × Nat × Nat) := [(9520181248,116261226209145,116261615979004)]
theorem point_links_checked72603 : (cuts72603.take 1).map (fun c => (9520152577-1+2*2^10*c.k,116261188098348+c.lower,116261577868187+c.upper)) = pointBounds72603 := by
 decide +kernel
def cuts72604 : List PrefixCut := [⟨64,168050900,168051009⟩]
theorem checked72604 : checkPrefixCuts (2^48) 9520283649 10 Manual.Count131072.C072604.packed 64 cuts72604 = true := by
 decide +kernel
def cuts72605 : List PrefixCut := [⟨32,83462845,83462893⟩,
⟨64,167102505,167102605⟩]
theorem checked72605 : checkPrefixCuts (2^48) 9520414721 10 Manual.Count131072.C072605.packed 64 cuts72605 = true := by
 decide +kernel
def pointBounds72605 : List (Nat × Nat × Nat) := [(9520480256,116261609202744,116261998972838)]
theorem point_links_checked72605 : (cuts72605.take 1).map (fun c => (9520414721-1+2*2^10*c.k,116261525739899+c.lower,116261915509945+c.upper)) = pointBounds72605 := by
 decide +kernel
def cuts72606 : List PrefixCut := [⟨64,172185346,172185447⟩]
theorem checked72606 : checkPrefixCuts (2^48) 9520545793 10 Manual.Count131072.C072606.packed 64 cuts72606 = true := by
 decide +kernel
def cuts72607 : List PrefixCut := [⟨50,129758275,129758355⟩,
⟨64,166683992,166684094⟩]
theorem checked72607 : checkPrefixCuts (2^48) 9520676865 10 Manual.Count131072.C072607.packed 64 cuts72607 = true := by
 decide +kernel
def pointBounds72607 : List (Nat × Nat × Nat) := [(9520779264,116261994786025,116262384556352)]
theorem point_links_checked72607 : (cuts72607.take 1).map (fun c => (9520676865-1+2*2^10*c.k,116261865027750+c.lower,116262254797997+c.upper)) = pointBounds72607 := by
 decide +kernel
def cuts72608 : List PrefixCut := [⟨64,170170248,170170352⟩]
theorem checked72608 : checkPrefixCuts (2^48) 9520807937 10 Manual.Count131072.C072608.packed 64 cuts72608 = true := by
 decide +kernel
def cuts72609 : List PrefixCut := [⟨64,170729617,170729722⟩]
theorem checked72609 : checkPrefixCuts (2^48) 9520939009 10 Manual.Count131072.C072609.packed 64 cuts72609 = true := by
 decide +kernel
def cuts72610 : List PrefixCut := [⟨4,10820188,10820194⟩,
⟨64,168421347,168421449⟩]
theorem checked72610 : checkPrefixCuts (2^48) 9521070081 10 Manual.Count131072.C072610.packed 64 cuts72610 = true := by
 decide +kernel
def pointBounds72610 : List (Nat × Nat × Nat) := [(9521078272,116262383431795,116262773202359)]
theorem point_links_checked72610 : (cuts72610.take 1).map (fun c => (9521070081-1+2*2^10*c.k,116262372611607+c.lower,116262762382165+c.upper)) = pointBounds72610 := by
 decide +kernel
def cuts72611 : List PrefixCut := [⟨64,169512847,169512952⟩]
theorem checked72611 : checkPrefixCuts (2^48) 9521201153 10 Manual.Count131072.C072611.packed 64 cuts72611 = true := by
 decide +kernel
def cuts72612 : List PrefixCut := [⟨22,59213656,59213691⟩,
⟨64,169776585,169776678⟩]
theorem checked72612 : checkPrefixCuts (2^48) 9521332225 10 Manual.Count131072.C072612.packed 64 cuts72612 = true := by
 decide +kernel
def pointBounds72612 : List (Nat × Nat × Nat) := [(9521377280,116262769759457,116263159530257)]
theorem point_links_checked72612 : (cuts72612.take 1).map (fun c => (9521332225-1+2*2^10*c.k,116262710545801+c.lower,116263100316566+c.upper)) = pointBounds72612 := by
 decide +kernel
def cuts72613 : List PrefixCut := [⟨64,167202328,167202433⟩]
theorem checked72613 : checkPrefixCuts (2^48) 9521463297 10 Manual.Count131072.C072613.packed 64 cuts72613 = true := by
 decide +kernel
def cuts72614 : List PrefixCut := [⟨40,104441179,104441242⟩,
⟨64,167998206,167998309⟩]
theorem checked72614 : checkPrefixCuts (2^48) 9521594369 10 Manual.Count131072.C072614.packed 64 cuts72614 = true := by
 decide +kernel
def pointBounds72614 : List (Nat × Nat × Nat) := [(9521676288,116263151965893,116263541736919)]
theorem point_links_checked72614 : (cuts72614.take 1).map (fun c => (9521594369-1+2*2^10*c.k,116263047524714+c.lower,116263437295677+c.upper)) = pointBounds72614 := by
 decide +kernel
def cuts72615 : List PrefixCut := [⟨64,168468884,168468981⟩]
theorem checked72615 : checkPrefixCuts (2^48) 9521725441 10 Manual.Count131072.C072615.packed 64 cuts72615 = true := by
 decide +kernel
def cuts72616 : List PrefixCut := [⟨58,153804535,153804629⟩,
⟨64,169619424,169619526⟩]
theorem checked72616 : checkPrefixCuts (2^48) 9521856513 10 Manual.Count131072.C072616.packed 64 cuts72616 = true := by
 decide +kernel
def pointBounds72616 : List (Nat × Nat × Nat) := [(9521975296,116263537796339,116263927567596)]
theorem point_links_checked72616 : (cuts72616.take 1).map (fun c => (9521856513-1+2*2^10*c.k,116263383991804+c.lower,116263773762967+c.upper)) = pointBounds72616 := by
 decide +kernel
def cuts72617 : List PrefixCut := [⟨64,166927097,166927191⟩]
theorem checked72617 : checkPrefixCuts (2^48) 9521987585 10 Manual.Count131072.C072617.packed 64 cuts72617 = true := by
 decide +kernel
def cuts72618 : List PrefixCut := [⟨64,168432367,168432466⟩]
theorem checked72618 : checkPrefixCuts (2^48) 9522118657 10 Manual.Count131072.C072618.packed 64 cuts72618 = true := by
 decide +kernel
def cuts72619 : List PrefixCut := [⟨12,31421925,31421945⟩,
⟨64,167779722,167779822⟩]
theorem checked72619 : checkPrefixCuts (2^48) 9522249729 10 Manual.Count131072.C072619.packed 64 cuts72619 = true := by
 decide +kernel
def pointBounds72619 : List (Nat × Nat × Nat) := [(9522274304,116263920392617,116264310164095)]
theorem point_links_checked72619 : (cuts72619.take 1).map (fun c => (9522249729-1+2*2^10*c.k,116263888970692+c.lower,116264278742150+c.upper)) = pointBounds72619 := by
 decide +kernel
def cuts72620 : List PrefixCut := [⟨64,167747864,167747961⟩]
theorem checked72620 : checkPrefixCuts (2^48) 9522380801 10 Manual.Count131072.C072620.packed 64 cuts72620 = true := by
 decide +kernel
def cuts72621 : List PrefixCut := [⟨30,79542721,79542765⟩,
⟨64,169193937,169194029⟩]
theorem checked72621 : checkPrefixCuts (2^48) 9522511873 10 Manual.Count131072.C072621.packed 64 cuts72621 = true := by
 decide +kernel
def pointBounds72621 : List (Nat × Nat × Nat) := [(9522573312,116264304040999,116264693812698)]
theorem point_links_checked72621 : (cuts72621.take 1).map (fun c => (9522511873-1+2*2^10*c.k,116264224498278+c.lower,116264614269933+c.upper)) = pointBounds72621 := by
 decide +kernel
def cuts72622 : List PrefixCut := [⟨64,167802354,167802453⟩]
theorem checked72622 : checkPrefixCuts (2^48) 9522642945 10 Manual.Count131072.C072622.packed 64 cuts72622 = true := by
 decide +kernel
def cuts72623 : List PrefixCut := [⟨48,128902103,128902176⟩,
⟨64,171731242,171731342⟩]
theorem checked72623 : checkPrefixCuts (2^48) 9522774017 10 Manual.Count131072.C072623.packed 64 cuts72623 = true := by
 decide +kernel
def pointBounds72623 : List (Nat × Nat × Nat) := [(9522872320,116264690396672,116265080168591)]
theorem point_links_checked72623 : (cuts72623.take 1).map (fun c => (9522774017-1+2*2^10*c.k,116264561494569+c.lower,116264951266415+c.upper)) = pointBounds72623 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000081
