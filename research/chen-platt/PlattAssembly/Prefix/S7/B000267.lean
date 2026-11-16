import PlattAssemblyKernel
import PlattCertificates.Count131072.C068544
import PlattCertificates.Count131072.C068545
import PlattCertificates.Count131072.C068546
import PlattCertificates.Count131072.C068547
import PlattCertificates.Count131072.C068548
import PlattCertificates.Count131072.C068549
import PlattCertificates.Count131072.C068550
import PlattCertificates.Count131072.C068551
import PlattCertificates.Count131072.C068552
import PlattCertificates.Count131072.C068553
import PlattCertificates.Count131072.C068554
import PlattCertificates.Count131072.C068555
import PlattCertificates.Count131072.C068556
import PlattCertificates.Count131072.C068557
import PlattCertificates.Count131072.C068558
import PlattCertificates.Count131072.C068559
import PlattCertificates.Count131072.C068560
import PlattCertificates.Count131072.C068561
import PlattCertificates.Count131072.C068562
import PlattCertificates.Count131072.C068563
import PlattCertificates.Count131072.C068564
import PlattCertificates.Count131072.C068565
import PlattCertificates.Count131072.C068566
import PlattCertificates.Count131072.C068567
import PlattCertificates.Count131072.C068568
import PlattCertificates.Count131072.C068569
import PlattCertificates.Count131072.C068570
import PlattCertificates.Count131072.C068571
import PlattCertificates.Count131072.C068572
import PlattCertificates.Count131072.C068573
import PlattCertificates.Count131072.C068574
import PlattCertificates.Count131072.C068575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000267
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68544 : List PrefixCut := [⟨64,180881544,180881654⟩]
theorem checked68544 : checkPrefixCuts (2^48) 8988131329 10 Manual.Count131072.C068544.packed 64 cuts68544 = true := by
 decide +kernel
def cuts68545 : List PrefixCut := [⟨43,122412976,122413042⟩,
⟨64,181693120,181693220⟩]
theorem checked68545 : checkPrefixCuts (2^48) 8988262401 10 Manual.Count131072.C068545.packed 64 cuts68545 = true := by
 decide +kernel
def pointBounds68545 : List (Nat × Nat × Nat) := [(8988350464,115556131910823,115556521264682)]
theorem point_links_checked68545 : (cuts68545.take 1).map (fun c => (8988262401-1+2*2^10*c.k,115556009497847+c.lower,115556398851640+c.upper)) = pointBounds68545 := by
 decide +kernel
def cuts68546 : List PrefixCut := [⟨64,178402369,178402476⟩]
theorem checked68546 : checkPrefixCuts (2^48) 8988393473 10 Manual.Count131072.C068546.packed 64 cuts68546 = true := by
 decide +kernel
def cuts68547 : List PrefixCut := [⟨53,149026795,149026886⟩,
⟨64,181061529,181061637⟩]
theorem checked68547 : checkPrefixCuts (2^48) 8988524545 10 Manual.Count131072.C068547.packed 64 cuts68547 = true := by
 decide +kernel
def pointBounds68547 : List (Nat × Nat × Nat) := [(8988633088,115556518620131,115556907974222)]
theorem point_links_checked68547 : (cuts68547.take 1).map (fun c => (8988524545-1+2*2^10*c.k,115556369593336+c.lower,115556758947336+c.upper)) = pointBounds68547 := by
 decide +kernel
def cuts68548 : List PrefixCut := [⟨64,179900261,179900359⟩]
theorem checked68548 : checkPrefixCuts (2^48) 8988655617 10 Manual.Count131072.C068548.packed 64 cuts68548 = true := by
 decide +kernel
def cuts68549 : List PrefixCut := [⟨63,174918761,174918868⟩,
⟨64,177956175,177956284⟩]
theorem checked68549 : checkPrefixCuts (2^48) 8988786689 10 Manual.Count131072.C068549.packed 64 cuts68549 = true := by
 decide +kernel
def pointBounds68549 : List (Nat × Nat × Nat) := [(8988915712,115556905473887,115557294828200)]
theorem point_links_checked68549 : (cuts68549.take 1).map (fun c => (8988786689-1+2*2^10*c.k,115556730555126+c.lower,115557119909332+c.upper)) = pointBounds68549 := by
 decide +kernel
def cuts68550 : List PrefixCut := [⟨64,176888935,176889041⟩]
theorem checked68550 : checkPrefixCuts (2^48) 8988917761 10 Manual.Count131072.C068550.packed 64 cuts68550 = true := by
 decide +kernel
def cuts68551 : List PrefixCut := [⟨64,179234831,179234938⟩]
theorem checked68551 : checkPrefixCuts (2^48) 8989048833 10 Manual.Count131072.C068551.packed 64 cuts68551 = true := by
 decide +kernel
def cuts68552 : List PrefixCut := [⟨9,26020770,26020786⟩,
⟨64,181518000,181518114⟩]
theorem checked68552 : checkPrefixCuts (2^48) 8989179905 10 Manual.Count131072.C068552.packed 64 cuts68552 = true := by
 decide +kernel
def pointBounds68552 : List (Nat × Nat × Nat) := [(8989198336,115557290655837,115557680010381)]
theorem point_links_checked68552 : (cuts68552.take 1).map (fun c => (8989179905-1+2*2^10*c.k,115557264635067+c.lower,115557653989595+c.upper)) = pointBounds68552 := by
 decide +kernel
def cuts68553 : List PrefixCut := [⟨64,176317584,176317690⟩]
theorem checked68553 : checkPrefixCuts (2^48) 8989310977 10 Manual.Count131072.C068553.packed 64 cuts68553 = true := by
 decide +kernel
def cuts68554 : List PrefixCut := [⟨19,55359005,55359037⟩,
⟨64,183266171,183266275⟩]
theorem checked68554 : checkPrefixCuts (2^48) 8989442049 10 Manual.Count131072.C068554.packed 64 cuts68554 = true := by
 decide +kernel
def pointBounds68554 : List (Nat × Nat × Nat) := [(8989480960,115557677829656,115558067184436)]
theorem point_links_checked68554 : (cuts68554.take 1).map (fun c => (8989442049-1+2*2^10*c.k,115557622470651+c.lower,115558011825399+c.upper)) = pointBounds68554 := by
 decide +kernel
def cuts68555 : List PrefixCut := [⟨64,179067815,179067918⟩]
theorem checked68555 : checkPrefixCuts (2^48) 8989573121 10 Manual.Count131072.C068555.packed 64 cuts68555 = true := by
 decide +kernel
def cuts68556 : List PrefixCut := [⟨29,81470448,81470496⟩,
⟨64,177844092,177844200⟩]
theorem checked68556 : checkPrefixCuts (2^48) 8989704193 10 Manual.Count131072.C068556.packed 64 cuts68556 = true := by
 decide +kernel
def pointBounds68556 : List (Nat × Nat × Nat) := [(8989763584,115558066275085,115558455630088)]
theorem point_links_checked68556 : (cuts68556.take 1).map (fun c => (8989704193-1+2*2^10*c.k,115557984804637+c.lower,115558374159592+c.upper)) = pointBounds68556 := by
 decide +kernel
def cuts68557 : List PrefixCut := [⟨64,179313056,179313165⟩]
theorem checked68557 : checkPrefixCuts (2^48) 8989835265 10 Manual.Count131072.C068557.packed 64 cuts68557 = true := by
 decide +kernel
def cuts68558 : List PrefixCut := [⟨39,108582222,108582287⟩,
⟨64,177588417,177588527⟩]
theorem checked68558 : checkPrefixCuts (2^48) 8989966337 10 Manual.Count131072.C068558.packed 64 cuts68558 = true := by
 decide +kernel
def pointBounds68558 : List (Nat × Nat × Nat) := [(8990046208,115558450544007,115558839899244)]
theorem point_links_checked68558 : (cuts68558.take 1).map (fun c => (8989966337-1+2*2^10*c.k,115558341961785+c.lower,115558731316957+c.upper)) = pointBounds68558 := by
 decide +kernel
def cuts68559 : List PrefixCut := [⟨64,177491896,177492004⟩]
theorem checked68559 : checkPrefixCuts (2^48) 8990097409 10 Manual.Count131072.C068559.packed 64 cuts68559 = true := by
 decide +kernel
def cuts68560 : List PrefixCut := [⟨49,136036772,136036857⟩,
⟨64,177771106,177771216⟩]
theorem checked68560 : checkPrefixCuts (2^48) 8990228481 10 Manual.Count131072.C068560.packed 64 cuts68560 = true := by
 decide +kernel
def pointBounds68560 : List (Nat × Nat × Nat) := [(8990328832,115558833078870,115559222434345)]
theorem point_links_checked68560 : (cuts68560.take 1).map (fun c => (8990228481-1+2*2^10*c.k,115558697042098+c.lower,115559086397488+c.upper)) = pointBounds68560 := by
 decide +kernel
def cuts68561 : List PrefixCut := [⟨64,180054015,180054121⟩]
theorem checked68561 : checkPrefixCuts (2^48) 8990359553 10 Manual.Count131072.C068561.packed 64 cuts68561 = true := by
 decide +kernel
def cuts68562 : List PrefixCut := [⟨59,167090032,167090129⟩,
⟨64,180333159,180333264⟩]
theorem checked68562 : checkPrefixCuts (2^48) 8990490625 10 Manual.Count131072.C068562.packed 64 cuts68562 = true := by
 decide +kernel
def pointBounds68562 : List (Nat × Nat × Nat) := [(8990611456,115559221957251,115559611312954)]
theorem point_links_checked68562 : (cuts68562.take 1).map (fun c => (8990490625-1+2*2^10*c.k,115559054867219+c.lower,115559444222825+c.upper)) = pointBounds68562 := by
 decide +kernel
def cuts68563 : List PrefixCut := [⟨64,178796469,178796577⟩]
theorem checked68563 : checkPrefixCuts (2^48) 8990621697 10 Manual.Count131072.C068563.packed 64 cuts68563 = true := by
 decide +kernel
def cuts68564 : List PrefixCut := [⟨64,180860122,180860234⟩]
theorem checked68564 : checkPrefixCuts (2^48) 8990752769 10 Manual.Count131072.C068564.packed 64 cuts68564 = true := by
 decide +kernel
def cuts68565 : List PrefixCut := [⟨5,14401072,14401082⟩,
⟨64,178259045,178259150⟩]
theorem checked68565 : checkPrefixCuts (2^48) 8990883841 10 Manual.Count131072.C068565.packed 64 cuts68565 = true := by
 decide +kernel
def pointBounds68565 : List (Nat × Nat × Nat) := [(8990894080,115559609258041,115559998613982)]
theorem point_links_checked68565 : (cuts68565.take 1).map (fun c => (8990883841-1+2*2^10*c.k,115559594856969+c.lower,115559984212900+c.upper)) = pointBounds68565 := by
 decide +kernel
def cuts68566 : List PrefixCut := [⟨64,180134800,180134904⟩]
theorem checked68566 : checkPrefixCuts (2^48) 8991014913 10 Manual.Count131072.C068566.packed 64 cuts68566 = true := by
 decide +kernel
def cuts68567 : List PrefixCut := [⟨15,42074905,42074928⟩,
⟨64,178911265,178911371⟩]
theorem checked68567 : checkPrefixCuts (2^48) 8991145985 10 Manual.Count131072.C068567.packed 64 cuts68567 = true := by
 decide +kernel
def pointBounds68567 : List (Nat × Nat × Nat) := [(8991176704,115559995325719,115560384681882)]
theorem point_links_checked68567 : (cuts68567.take 1).map (fun c => (8991145985-1+2*2^10*c.k,115559953250814+c.lower,115560342606954+c.upper)) = pointBounds68567 := by
 decide +kernel
def cuts68568 : List PrefixCut := [⟨64,179785198,179785307⟩]
theorem checked68568 : checkPrefixCuts (2^48) 8991277057 10 Manual.Count131072.C068568.packed 64 cuts68568 = true := by
 decide +kernel
def cuts68569 : List PrefixCut := [⟨25,69496621,69496659⟩,
⟨64,178686914,178687022⟩]
theorem checked68569 : checkPrefixCuts (2^48) 8991408129 10 Manual.Count131072.C068569.packed 64 cuts68569 = true := by
 decide +kernel
def pointBounds68569 : List (Nat × Nat × Nat) := [(8991459328,115560381443898,115560770800291)]
theorem point_links_checked68569 : (cuts68569.take 1).map (fun c => (8991408129-1+2*2^10*c.k,115560311947277+c.lower,115560701303632+c.upper)) = pointBounds68569 := by
 decide +kernel
def cuts68570 : List PrefixCut := [⟨64,179999087,179999190⟩]
theorem checked68570 : checkPrefixCuts (2^48) 8991539201 10 Manual.Count131072.C068570.packed 64 cuts68570 = true := by
 decide +kernel
def cuts68571 : List PrefixCut := [⟨35,97855794,97855847⟩,
⟨64,178399973,178400074⟩]
theorem checked68571 : checkPrefixCuts (2^48) 8991670273 10 Manual.Count131072.C068571.packed 64 cuts68571 = true := by
 decide +kernel
def pointBounds68571 : List (Nat × Nat × Nat) := [(8991741952,115560768489072,115561157845691)]
theorem point_links_checked68571 : (cuts68571.take 1).map (fun c => (8991670273-1+2*2^10*c.k,115560670633278+c.lower,115561059989844+c.upper)) = pointBounds68571 := by
 decide +kernel
def cuts68572 : List PrefixCut := [⟨64,180400789,180400894⟩]
theorem checked68572 : checkPrefixCuts (2^48) 8991801345 10 Manual.Count131072.C068572.packed 64 cuts68572 = true := by
 decide +kernel
def cuts68573 : List PrefixCut := [⟨45,126056729,126056801⟩,
⟨64,179333857,179333963⟩]
theorem checked68573 : checkPrefixCuts (2^48) 8991932417 10 Manual.Count131072.C068573.packed 64 cuts68573 = true := by
 decide +kernel
def pointBounds68573 : List (Nat × Nat × Nat) := [(8992024576,115561155490769,115561544847613)]
theorem point_links_checked68573 : (cuts68573.take 1).map (fun c => (8991932417-1+2*2^10*c.k,115561029434040+c.lower,115561418790812+c.upper)) = pointBounds68573 := by
 decide +kernel
def cuts68574 : List PrefixCut := [⟨64,179143422,179143523⟩]
theorem checked68574 : checkPrefixCuts (2^48) 8992063489 10 Manual.Count131072.C068574.packed 64 cuts68574 = true := by
 decide +kernel
def cuts68575 : List PrefixCut := [⟨55,153504711,153504797⟩,
⟨64,178389571,178389673⟩]
theorem checked68575 : checkPrefixCuts (2^48) 8992194561 10 Manual.Count131072.C068575.packed 64 cuts68575 = true := by
 decide +kernel
def pointBounds68575 : List (Nat × Nat × Nat) := [(8992307200,115561541416030,115561930773095)]
theorem point_links_checked68575 : (cuts68575.take 1).map (fun c => (8992194561-1+2*2^10*c.k,115561387911319+c.lower,115561777268298+c.upper)) = pointBounds68575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000267
