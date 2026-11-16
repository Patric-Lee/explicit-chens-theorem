import PlattAssemblyKernel
import PlattCertificates.Count131072.C068576
import PlattCertificates.Count131072.C068577
import PlattCertificates.Count131072.C068578
import PlattCertificates.Count131072.C068579
import PlattCertificates.Count131072.C068580
import PlattCertificates.Count131072.C068581
import PlattCertificates.Count131072.C068582
import PlattCertificates.Count131072.C068583
import PlattCertificates.Count131072.C068584
import PlattCertificates.Count131072.C068585
import PlattCertificates.Count131072.C068586
import PlattCertificates.Count131072.C068587
import PlattCertificates.Count131072.C068588
import PlattCertificates.Count131072.C068589
import PlattCertificates.Count131072.C068590
import PlattCertificates.Count131072.C068591
import PlattCertificates.Count131072.C068592
import PlattCertificates.Count131072.C068593
import PlattCertificates.Count131072.C068594
import PlattCertificates.Count131072.C068595
import PlattCertificates.Count131072.C068596
import PlattCertificates.Count131072.C068597
import PlattCertificates.Count131072.C068598
import PlattCertificates.Count131072.C068599
import PlattCertificates.Count131072.C068600
import PlattCertificates.Count131072.C068601
import PlattCertificates.Count131072.C068602
import PlattCertificates.Count131072.C068603
import PlattCertificates.Count131072.C068604
import PlattCertificates.Count131072.C068605
import PlattCertificates.Count131072.C068606
import PlattCertificates.Count131072.C068607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000268
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68576 : List PrefixCut := [⟨64,176821901,176822006⟩]
theorem checked68576 : checkPrefixCuts (2^48) 8992325633 10 Manual.Count131072.C068576.packed 64 cuts68576 = true := by
 decide +kernel
def cuts68577 : List PrefixCut := [⟨64,177038445,177038551⟩]
theorem checked68577 : checkPrefixCuts (2^48) 8992456705 10 Manual.Count131072.C068577.packed 64 cuts68577 = true := by
 decide +kernel
def cuts68578 : List PrefixCut := [⟨1,2566663,2566664⟩,
⟨64,181480519,181480625⟩]
theorem checked68578 : checkPrefixCuts (2^48) 8992587777 10 Manual.Count131072.C068578.packed 64 cuts68578 = true := by
 decide +kernel
def pointBounds68578 : List (Nat × Nat × Nat) := [(8992589824,115561922727899,115562312085192)]
theorem point_links_checked68578 : (cuts68578.take 1).map (fun c => (8992587777-1+2*2^10*c.k,115561920161236+c.lower,115562309518528+c.upper)) = pointBounds68578 := by
 decide +kernel
def cuts68579 : List PrefixCut := [⟨64,179787668,179787776⟩]
theorem checked68579 : checkPrefixCuts (2^48) 8992718849 10 Manual.Count131072.C068579.packed 64 cuts68579 = true := by
 decide +kernel
def cuts68580 : List PrefixCut := [⟨11,31237214,31237233⟩,
⟨64,179159055,179159166⟩]
theorem checked68580 : checkPrefixCuts (2^48) 8992849921 10 Manual.Count131072.C068580.packed 64 cuts68580 = true := by
 decide +kernel
def pointBounds68580 : List (Nat × Nat × Nat) := [(8992872448,115562312666637,115562702024162)]
theorem point_links_checked68580 : (cuts68580.take 1).map (fun c => (8992849921-1+2*2^10*c.k,115562281429423+c.lower,115562670786929+c.upper)) = pointBounds68580 := by
 decide +kernel
def cuts68581 : List PrefixCut := [⟨64,180314520,180314625⟩]
theorem checked68581 : checkPrefixCuts (2^48) 8992980993 10 Manual.Count131072.C068581.packed 64 cuts68581 = true := by
 decide +kernel
def cuts68582 : List PrefixCut := [⟨21,59342650,59342682⟩,
⟨64,178746956,178747058⟩]
theorem checked68582 : checkPrefixCuts (2^48) 8993112065 10 Manual.Count131072.C068582.packed 64 cuts68582 = true := by
 decide +kernel
def pointBounds68582 : List (Nat × Nat × Nat) := [(8993155072,115562700245648,115563089603402)]
theorem point_links_checked68582 : (cuts68582.take 1).map (fun c => (8993112065-1+2*2^10*c.k,115562640902998+c.lower,115563030260720+c.upper)) = pointBounds68582 := by
 decide +kernel
def cuts68583 : List PrefixCut := [⟨64,180559649,180559755⟩]
theorem checked68583 : checkPrefixCuts (2^48) 8993243137 10 Manual.Count131072.C068583.packed 64 cuts68583 = true := by
 decide +kernel
def cuts68584 : List PrefixCut := [⟨31,86789127,86789179⟩,
⟨64,178366173,178366282⟩]
theorem checked68584 : checkPrefixCuts (2^48) 8993374209 10 Manual.Count131072.C068584.packed 64 cuts68584 = true := by
 decide +kernel
def pointBounds68584 : List (Nat × Nat × Nat) := [(8993437696,115563086998730,115563476356712)]
theorem point_links_checked68584 : (cuts68584.take 1).map (fun c => (8993374209-1+2*2^10*c.k,115563000209603+c.lower,115563389567533+c.upper)) = pointBounds68584 := by
 decide +kernel
def cuts68585 : List PrefixCut := [⟨64,180116219,180116327⟩]
theorem checked68585 : checkPrefixCuts (2^48) 8993505281 10 Manual.Count131072.C068585.packed 64 cuts68585 = true := by
 decide +kernel
def cuts68586 : List PrefixCut := [⟨41,113107256,113107324⟩,
⟨64,175732038,175732141⟩]
theorem checked68586 : checkPrefixCuts (2^48) 8993636353 10 Manual.Count131072.C068586.packed 64 cuts68586 = true := by
 decide +kernel
def pointBounds68586 : List (Nat × Nat × Nat) := [(8993720320,115563471799251,115563861157466)]
theorem point_links_checked68586 : (cuts68586.take 1).map (fun c => (8993636353-1+2*2^10*c.k,115563358691995+c.lower,115563748050142+c.upper)) = pointBounds68586 := by
 decide +kernel
def cuts68587 : List PrefixCut := [⟨64,179359853,179359965⟩]
theorem checked68587 : checkPrefixCuts (2^48) 8993767425 10 Manual.Count131072.C068587.packed 64 cuts68587 = true := by
 decide +kernel
def cuts68588 : List PrefixCut := [⟨51,143711347,143711426⟩,
⟨64,180077060,180077163⟩]
theorem checked68588 : checkPrefixCuts (2^48) 8993898497 10 Manual.Count131072.C068588.packed 64 cuts68588 = true := by
 decide +kernel
def pointBounds68588 : List (Nat × Nat × Nat) := [(8994002944,115563857495233,115564246853674)]
theorem point_links_checked68588 : (cuts68588.take 1).map (fun c => (8993898497-1+2*2^10*c.k,115563713783886+c.lower,115564103142248+c.upper)) = pointBounds68588 := by
 decide +kernel
def cuts68589 : List PrefixCut := [⟨64,179323344,179323447⟩]
theorem checked68589 : checkPrefixCuts (2^48) 8994029569 10 Manual.Count131072.C068589.packed 64 cuts68589 = true := by
 decide +kernel
def cuts68590 : List PrefixCut := [⟨61,168962110,168962210⟩,
⟨64,177286539,177286645⟩]
theorem checked68590 : checkPrefixCuts (2^48) 8994160641 10 Manual.Count131072.C068590.packed 64 cuts68590 = true := by
 decide +kernel
def pointBounds68590 : List (Nat × Nat × Nat) := [(8994285568,115564242146400,115564631505068)]
theorem point_links_checked68590 : (cuts68590.take 1).map (fun c => (8994160641-1+2*2^10*c.k,115564073184290+c.lower,115564462542858+c.upper)) = pointBounds68590 := by
 decide +kernel
def cuts68591 : List PrefixCut := [⟨64,179161627,179161739⟩]
theorem checked68591 : checkPrefixCuts (2^48) 8994291713 10 Manual.Count131072.C068591.packed 64 cuts68591 = true := by
 decide +kernel
def cuts68592 : List PrefixCut := [⟨64,177844690,177844793⟩]
theorem checked68592 : checkPrefixCuts (2^48) 8994422785 10 Manual.Count131072.C068592.packed 64 cuts68592 = true := by
 decide +kernel
def cuts68593 : List PrefixCut := [⟨7,19902921,19902932⟩,
⟨64,179500631,179500739⟩]
theorem checked68593 : checkPrefixCuts (2^48) 8994553857 10 Manual.Count131072.C068593.packed 64 cuts68593 = true := by
 decide +kernel
def pointBounds68593 : List (Nat × Nat × Nat) := [(8994568192,115564627380067,115565016738967)]
theorem point_links_checked68593 : (cuts68593.take 1).map (fun c => (8994553857-1+2*2^10*c.k,115564607477146+c.lower,115564996836035+c.upper)) = pointBounds68593 := by
 decide +kernel
def cuts68594 : List PrefixCut := [⟨64,179341562,179341669⟩]
theorem checked68594 : checkPrefixCuts (2^48) 8994684929 10 Manual.Count131072.C068594.packed 64 cuts68594 = true := by
 decide +kernel
def cuts68595 : List PrefixCut := [⟨17,46657790,46657818⟩,
⟨64,178869560,178869659⟩]
theorem checked68595 : checkPrefixCuts (2^48) 8994816001 10 Manual.Count131072.C068595.packed 64 cuts68595 = true := by
 decide +kernel
def pointBounds68595 : List (Nat × Nat × Nat) := [(8994850816,115565012977129,115565402336261)]
theorem point_links_checked68595 : (cuts68595.take 1).map (fun c => (8994816001-1+2*2^10*c.k,115564966319339+c.lower,115565355678443+c.upper)) = pointBounds68595 := by
 decide +kernel
def cuts68596 : List PrefixCut := [⟨64,176864234,176864341⟩]
theorem checked68596 : checkPrefixCuts (2^48) 8994947073 10 Manual.Count131072.C068596.packed 64 cuts68596 = true := by
 decide +kernel
def cuts68597 : List PrefixCut := [⟨27,76759292,76759336⟩,
⟨64,181086078,181086180⟩]
theorem checked68597 : checkPrefixCuts (2^48) 8995078145 10 Manual.Count131072.C068597.packed 64 cuts68597 = true := by
 decide +kernel
def pointBounds68597 : List (Nat × Nat × Nat) := [(8995133440,115565398812425,115565788171779)]
theorem point_links_checked68597 : (cuts68597.take 1).map (fun c => (8995078145-1+2*2^10*c.k,115565322053133+c.lower,115565711412443+c.upper)) = pointBounds68597 := by
 decide +kernel
def cuts68598 : List PrefixCut := [⟨64,180614068,180614175⟩]
theorem checked68598 : checkPrefixCuts (2^48) 8995209217 10 Manual.Count131072.C068598.packed 64 cuts68598 = true := by
 decide +kernel
def cuts68599 : List PrefixCut := [⟨37,103291781,103291845⟩,
⟨64,178577514,178577625⟩]
theorem checked68599 : checkPrefixCuts (2^48) 8995340289 10 Manual.Count131072.C068599.packed 64 cuts68599 = true := by
 decide +kernel
def pointBounds68599 : List (Nat × Nat × Nat) := [(8995416064,115565787045060,115566176404643)]
theorem point_links_checked68599 : (cuts68599.take 1).map (fun c => (8995340289-1+2*2^10*c.k,115565683753279+c.lower,115566073112798+c.upper)) = pointBounds68599 := by
 decide +kernel
def cuts68600 : List PrefixCut := [⟨64,180295891,180295996⟩]
theorem checked68600 : checkPrefixCuts (2^48) 8995471361 10 Manual.Count131072.C068600.packed 64 cuts68600 = true := by
 decide +kernel
def cuts68601 : List PrefixCut := [⟨47,132106848,132106928⟩,
⟨64,180324556,180324662⟩]
theorem checked68601 : checkPrefixCuts (2^48) 8995602433 10 Manual.Count131072.C068601.packed 64 cuts68601 = true := by
 decide +kernel
def pointBounds68601 : List (Nat × Nat × Nat) := [(8995698688,115566174733532,115566564093347)]
theorem point_links_checked68601 : (cuts68601.take 1).map (fun c => (8995602433-1+2*2^10*c.k,115566042626684+c.lower,115566431986419+c.upper)) = pointBounds68601 := by
 decide +kernel
def cuts68602 : List PrefixCut := [⟨64,177599732,177599827⟩]
theorem checked68602 : checkPrefixCuts (2^48) 8995733505 10 Manual.Count131072.C068602.packed 64 cuts68602 = true := by
 decide +kernel
def cuts68603 : List PrefixCut := [⟨57,158980237,158980324⟩,
⟨64,178629689,178629786⟩]
theorem checked68603 : checkPrefixCuts (2^48) 8995864577 10 Manual.Count131072.C068603.packed 64 cuts68603 = true := by
 decide +kernel
def pointBounds68603 : List (Nat × Nat × Nat) := [(8995981312,115566559531209,115566948891232)]
theorem point_links_checked68603 : (cuts68603.take 1).map (fun c => (8995864577-1+2*2^10*c.k,115566400550972+c.lower,115566789910908+c.upper)) = pointBounds68603 := by
 decide +kernel
def cuts68604 : List PrefixCut := [⟨64,179909924,179910029⟩]
theorem checked68604 : checkPrefixCuts (2^48) 8995995649 10 Manual.Count131072.C068604.packed 64 cuts68604 = true := by
 decide +kernel
def cuts68605 : List PrefixCut := [⟨64,179782143,179782251⟩]
theorem checked68605 : checkPrefixCuts (2^48) 8996126721 10 Manual.Count131072.C068605.packed 64 cuts68605 = true := by
 decide +kernel
def cuts68606 : List PrefixCut := [⟨3,8197452,8197457⟩,
⟨64,178747041,178747143⟩]
theorem checked68606 : checkPrefixCuts (2^48) 8996257793 10 Manual.Count131072.C068606.packed 64 cuts68606 = true := by
 decide +kernel
def pointBounds68606 : List (Nat × Nat × Nat) := [(8996263936,115566947070180,115567336430431)]
theorem point_links_checked68606 : (cuts68606.take 1).map (fun c => (8996257793-1+2*2^10*c.k,115566938872728+c.lower,115567328232974+c.upper)) = pointBounds68606 := by
 decide +kernel
def cuts68607 : List PrefixCut := [⟨64,178118684,178118789⟩]
theorem checked68607 : checkPrefixCuts (2^48) 8996388865 10 Manual.Count131072.C068607.packed 64 cuts68607 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000268
