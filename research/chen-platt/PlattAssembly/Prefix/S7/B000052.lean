import PlattAssemblyKernel
import PlattCertificates.Count131072.C061664
import PlattCertificates.Count131072.C061665
import PlattCertificates.Count131072.C061666
import PlattCertificates.Count131072.C061667
import PlattCertificates.Count131072.C061668
import PlattCertificates.Count131072.C061669
import PlattCertificates.Count131072.C061670
import PlattCertificates.Count131072.C061671
import PlattCertificates.Count131072.C061672
import PlattCertificates.Count131072.C061673
import PlattCertificates.Count131072.C061674
import PlattCertificates.Count131072.C061675
import PlattCertificates.Count131072.C061676
import PlattCertificates.Count131072.C061677
import PlattCertificates.Count131072.C061678
import PlattCertificates.Count131072.C061679
import PlattCertificates.Count131072.C061680
import PlattCertificates.Count131072.C061681
import PlattCertificates.Count131072.C061682
import PlattCertificates.Count131072.C061683
import PlattCertificates.Count131072.C061684
import PlattCertificates.Count131072.C061685
import PlattCertificates.Count131072.C061686
import PlattCertificates.Count131072.C061687
import PlattCertificates.Count131072.C061688
import PlattCertificates.Count131072.C061689
import PlattCertificates.Count131072.C061690
import PlattCertificates.Count131072.C061691
import PlattCertificates.Count131072.C061692
import PlattCertificates.Count131072.C061693
import PlattCertificates.Count131072.C061694
import PlattCertificates.Count131072.C061695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61664 : List PrefixCut := [⟨32,99308589,99308646⟩,
⟨64,196319028,196319145⟩]
theorem checked61664 : checkPrefixCuts (2^48) 8086355969 10 Manual.Count131072.C061664.packed 64 cuts61664 = true := by
 decide +kernel
def pointBounds61664 : List (Nat × Nat × Nat) := [(8086421504,114254502982679,114254891583117)]
theorem point_links_checked61664 : (cuts61664.take 1).map (fun c => (8086355969-1+2*2^10*c.k,114254403674090+c.lower,114254792274471+c.upper)) = pointBounds61664 := by
 decide +kernel
def cuts61665 : List PrefixCut := [⟨64,201711048,201711163⟩]
theorem checked61665 : checkPrefixCuts (2^48) 8086487041 10 Manual.Count131072.C061665.packed 64 cuts61665 = true := by
 decide +kernel
def cuts61666 : List PrefixCut := [⟨28,87192459,87192509⟩,
⟨64,199062432,199062551⟩]
theorem checked61666 : checkPrefixCuts (2^48) 8086618113 10 Manual.Count131072.C061666.packed 64 cuts61666 = true := by
 decide +kernel
def pointBounds61666 : List (Nat × Nat × Nat) := [(8086675456,114254888896625,114255277497288)]
theorem point_links_checked61666 : (cuts61666.take 1).map (fun c => (8086618113-1+2*2^10*c.k,114254801704166+c.lower,114255190304779+c.upper)) = pointBounds61666 := by
 decide +kernel
def cuts61667 : List PrefixCut := [⟨64,199198433,199198549⟩]
theorem checked61667 : checkPrefixCuts (2^48) 8086749185 10 Manual.Count131072.C061667.packed 64 cuts61667 = true := by
 decide +kernel
def cuts61668 : List PrefixCut := [⟨24,75320743,75320785⟩,
⟨64,201353187,201353300⟩]
theorem checked61668 : checkPrefixCuts (2^48) 8086880257 10 Manual.Count131072.C061668.packed 64 cuts61668 = true := by
 decide +kernel
def pointBounds61668 : List (Nat × Nat × Nat) := [(8086929408,114255275285774,114255663886664)]
theorem point_links_checked61668 : (cuts61668.take 1).map (fun c => (8086880257-1+2*2^10*c.k,114255199965031+c.lower,114255588565879+c.upper)) = pointBounds61668 := by
 decide +kernel
def cuts61669 : List PrefixCut := [⟨64,204238784,204238894⟩]
theorem checked61669 : checkPrefixCuts (2^48) 8087011329 10 Manual.Count131072.C061669.packed 64 cuts61669 = true := by
 decide +kernel
def cuts61670 : List PrefixCut := [⟨20,63380174,63380210⟩,
⟨64,198805904,198806017⟩]
theorem checked61670 : checkPrefixCuts (2^48) 8087142401 10 Manual.Count131072.C061670.packed 64 cuts61670 = true := by
 decide +kernel
def pointBounds61670 : List (Nat × Nat × Nat) := [(8087183360,114255668937176,114256057538283)]
theorem point_links_checked61670 : (cuts61670.take 1).map (fun c => (8087142401-1+2*2^10*c.k,114255605557002+c.lower,114255994158073+c.upper)) = pointBounds61670 := by
 decide +kernel
def cuts61671 : List PrefixCut := [⟨64,202735581,202735701⟩]
theorem checked61671 : checkPrefixCuts (2^48) 8087273473 10 Manual.Count131072.C061671.packed 64 cuts61671 = true := by
 decide +kernel
def cuts61672 : List PrefixCut := [⟨16,47681528,47681558⟩,
⟨64,196189151,196189268⟩]
theorem checked61672 : checkPrefixCuts (2^48) 8087404545 10 Manual.Count131072.C061672.packed 64 cuts61672 = true := by
 decide +kernel
def pointBounds61672 : List (Nat × Nat × Nat) := [(8087437312,114256054780015,114256443381349)]
theorem point_links_checked61672 : (cuts61672.take 1).map (fun c => (8087404545-1+2*2^10*c.k,114256007098487+c.lower,114256395699791+c.upper)) = pointBounds61672 := by
 decide +kernel
def cuts61673 : List PrefixCut := [⟨64,199387891,199388001⟩]
theorem checked61673 : checkPrefixCuts (2^48) 8087535617 10 Manual.Count131072.C061673.packed 64 cuts61673 = true := by
 decide +kernel
def cuts61674 : List PrefixCut := [⟨12,38213613,38213637⟩,
⟨64,201925255,201925375⟩]
theorem checked61674 : checkPrefixCuts (2^48) 8087666689 10 Manual.Count131072.C061674.packed 64 cuts61674 = true := by
 decide +kernel
def pointBounds61674 : List (Nat × Nat × Nat) := [(8087691264,114256440889142,114256829490697)]
theorem point_links_checked61674 : (cuts61674.take 1).map (fun c => (8087666689-1+2*2^10*c.k,114256402675529+c.lower,114256791277060+c.upper)) = pointBounds61674 := by
 decide +kernel
def cuts61675 : List PrefixCut := [⟨64,199764242,199764358⟩]
theorem checked61675 : checkPrefixCuts (2^48) 8087797761 10 Manual.Count131072.C061675.packed 64 cuts61675 = true := by
 decide +kernel
def cuts61676 : List PrefixCut := [⟨8,25962155,25962169⟩,
⟨64,199030186,199030303⟩]
theorem checked61676 : checkPrefixCuts (2^48) 8087928833 10 Manual.Count131072.C061676.packed 64 cuts61676 = true := by
 decide +kernel
def pointBounds61676 : List (Nat × Nat × Nat) := [(8087945216,114256830327181,114257218928962)]
theorem point_links_checked61676 : (cuts61676.take 1).map (fun c => (8087928833-1+2*2^10*c.k,114256804365026+c.lower,114257192966793+c.upper)) = pointBounds61676 := by
 decide +kernel
def cuts61677 : List PrefixCut := [⟨64,199618567,199618681⟩]
theorem checked61677 : checkPrefixCuts (2^48) 8088059905 10 Manual.Count131072.C061677.packed 64 cuts61677 = true := by
 decide +kernel
def cuts61678 : List PrefixCut := [⟨4,12110645,12110653⟩,
⟨64,197944910,197945019⟩]
theorem checked61678 : checkPrefixCuts (2^48) 8088190977 10 Manual.Count131072.C061678.packed 64 cuts61678 = true := by
 decide +kernel
def pointBounds61678 : List (Nat × Nat × Nat) := [(8088199168,114257215124424,114257603726430)]
theorem point_links_checked61678 : (cuts61678.take 1).map (fun c => (8088190977-1+2*2^10*c.k,114257203013779+c.lower,114257591615777+c.upper)) = pointBounds61678 := by
 decide +kernel
def cuts61679 : List PrefixCut := [⟨64,198011313,198011426⟩]
theorem checked61679 : checkPrefixCuts (2^48) 8088322049 10 Manual.Count131072.C061679.packed 64 cuts61679 = true := by
 decide +kernel
def pointBounds61679 : List (Nat × Nat × Nat) := [(8088453120,114257598970002,114257987572222)]
theorem point_links_checked61679 : (cuts61679.take 1).map (fun c => (8088322049-1+2*2^10*c.k,114257400958689+c.lower,114257789560796+c.upper)) = pointBounds61679 := by
 decide +kernel
def cuts61680 : List PrefixCut := [⟨64,201140023,201140133⟩]
theorem checked61680 : checkPrefixCuts (2^48) 8088453121 10 Manual.Count131072.C061680.packed 64 cuts61680 = true := by
 decide +kernel
def cuts61681 : List PrefixCut := [⟨60,186208200,186208306⟩,
⟨64,199048841,199048955⟩]
theorem checked61681 : checkPrefixCuts (2^48) 8088584193 10 Manual.Count131072.C061681.packed 64 cuts61681 = true := by
 decide +kernel
def pointBounds61681 : List (Nat × Nat × Nat) := [(8088707072,114257986318225,114258374920661)]
theorem point_links_checked61681 : (cuts61681.take 1).map (fun c => (8088584193-1+2*2^10*c.k,114257800110025+c.lower,114258188712355+c.upper)) = pointBounds61681 := by
 decide +kernel
def cuts61682 : List PrefixCut := [⟨64,200507153,200507267⟩]
theorem checked61682 : checkPrefixCuts (2^48) 8088715265 10 Manual.Count131072.C061682.packed 64 cuts61682 = true := by
 decide +kernel
def cuts61683 : List PrefixCut := [⟨56,173466324,173466424⟩,
⟨64,198694422,198694535⟩]
theorem checked61683 : checkPrefixCuts (2^48) 8088846337 10 Manual.Count131072.C061683.packed 64 cuts61683 = true := by
 decide +kernel
def pointBounds61683 : List (Nat × Nat × Nat) := [(8088961024,114258373132343,114258761735001)]
theorem point_links_checked61683 : (cuts61683.take 1).map (fun c => (8088846337-1+2*2^10*c.k,114258199666019+c.lower,114258588268577+c.upper)) = pointBounds61683 := by
 decide +kernel
def cuts61684 : List PrefixCut := [⟨64,198169251,198169364⟩]
theorem checked61684 : checkPrefixCuts (2^48) 8088977409 10 Manual.Count131072.C061684.packed 64 cuts61684 = true := by
 decide +kernel
def cuts61685 : List PrefixCut := [⟨52,163682960,163683055⟩,
⟨64,201680481,201680598⟩]
theorem checked61685 : checkPrefixCuts (2^48) 8089108481 10 Manual.Count131072.C061685.packed 64 cuts61685 = true := by
 decide +kernel
def pointBounds61685 : List (Nat × Nat × Nat) := [(8089214976,114258760212652,114259148815531)]
theorem point_links_checked61685 : (cuts61685.take 1).map (fun c => (8089108481-1+2*2^10*c.k,114258596529692+c.lower,114258985132476+c.upper)) = pointBounds61685 := by
 decide +kernel
def cuts61686 : List PrefixCut := [⟨64,199415480,199415587⟩]
theorem checked61686 : checkPrefixCuts (2^48) 8089239553 10 Manual.Count131072.C061686.packed 64 cuts61686 = true := by
 decide +kernel
def cuts61687 : List PrefixCut := [⟨48,150733828,150733916⟩,
⟨64,201117212,201117328⟩]
theorem checked61687 : checkPrefixCuts (2^48) 8089370625 10 Manual.Count131072.C061687.packed 64 cuts61687 = true := by
 decide +kernel
def pointBounds61687 : List (Nat × Nat × Nat) := [(8089468928,114259148359481,114259536962577)]
theorem point_links_checked61687 : (cuts61687.take 1).map (fun c => (8089370625-1+2*2^10*c.k,114258997625653+c.lower,114259386228661+c.upper)) = pointBounds61687 := by
 decide +kernel
def cuts61688 : List PrefixCut := [⟨64,198504331,198504451⟩]
theorem checked61688 : checkPrefixCuts (2^48) 8089501697 10 Manual.Count131072.C061688.packed 64 cuts61688 = true := by
 decide +kernel
def cuts61689 : List PrefixCut := [⟨44,136428569,136428649⟩,
⟨64,197909644,197909761⟩]
theorem checked61689 : checkPrefixCuts (2^48) 8089632769 10 Manual.Count131072.C061689.packed 64 cuts61689 = true := by
 decide +kernel
def pointBounds61689 : List (Nat × Nat × Nat) := [(8089722880,114259533675765,114259922279089)]
theorem point_links_checked61689 : (cuts61689.take 1).map (fun c => (8089632769-1+2*2^10*c.k,114259397247196+c.lower,114259785850440+c.upper)) = pointBounds61689 := by
 decide +kernel
def cuts61690 : List PrefixCut := [⟨64,202081672,202081790⟩]
theorem checked61690 : checkPrefixCuts (2^48) 8089763841 10 Manual.Count131072.C061690.packed 64 cuts61690 = true := by
 decide +kernel
def cuts61691 : List PrefixCut := [⟨40,122959229,122959299⟩,
⟨64,196128770,196128883⟩]
theorem checked61691 : checkPrefixCuts (2^48) 8089894913 10 Manual.Count131072.C061691.packed 64 cuts61691 = true := by
 decide +kernel
def pointBounds61691 : List (Nat × Nat × Nat) := [(8089976832,114259920197741,114260308801290)]
theorem point_links_checked61691 : (cuts61691.take 1).map (fun c => (8089894913-1+2*2^10*c.k,114259797238512+c.lower,114260185841991+c.upper)) = pointBounds61691 := by
 decide +kernel
def cuts61692 : List PrefixCut := [⟨64,201761976,201762094⟩]
theorem checked61692 : checkPrefixCuts (2^48) 8090025985 10 Manual.Count131072.C061692.packed 64 cuts61692 = true := by
 decide +kernel
def cuts61693 : List PrefixCut := [⟨36,111056406,111056467⟩,
⟨64,197618470,197618580⟩]
theorem checked61693 : checkPrefixCuts (2^48) 8090157057 10 Manual.Count131072.C061693.packed 64 cuts61693 = true := by
 decide +kernel
def pointBounds61693 : List (Nat × Nat × Nat) := [(8090230784,114260306185664,114260694789435)]
theorem point_links_checked61693 : (cuts61693.take 1).map (fun c => (8090157057-1+2*2^10*c.k,114260195129258+c.lower,114260583732968+c.upper)) = pointBounds61693 := by
 decide +kernel
def cuts61694 : List PrefixCut := [⟨64,200120249,200120365⟩]
theorem checked61694 : checkPrefixCuts (2^48) 8090288129 10 Manual.Count131072.C061694.packed 64 cuts61694 = true := by
 decide +kernel
def cuts61695 : List PrefixCut := [⟨32,100893894,100893953⟩,
⟨64,200012641,200012757⟩]
theorem checked61695 : checkPrefixCuts (2^48) 8090419201 10 Manual.Count131072.C061695.packed 64 cuts61695 = true := by
 decide +kernel
def pointBounds61695 : List (Nat × Nat × Nat) := [(8090484736,114260693761871,114261082365866)]
theorem point_links_checked61695 : (cuts61695.take 1).map (fun c => (8090419201-1+2*2^10*c.k,114260592867977+c.lower,114260981471913+c.upper)) = pointBounds61695 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000052
