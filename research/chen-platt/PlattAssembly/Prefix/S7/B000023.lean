import PlattAssemblyKernel
import PlattCertificates.Count131072.C060736
import PlattCertificates.Count131072.C060737
import PlattCertificates.Count131072.C060738
import PlattCertificates.Count131072.C060739
import PlattCertificates.Count131072.C060740
import PlattCertificates.Count131072.C060741
import PlattCertificates.Count131072.C060742
import PlattCertificates.Count131072.C060743
import PlattCertificates.Count131072.C060744
import PlattCertificates.Count131072.C060745
import PlattCertificates.Count131072.C060746
import PlattCertificates.Count131072.C060747
import PlattCertificates.Count131072.C060748
import PlattCertificates.Count131072.C060749
import PlattCertificates.Count131072.C060750
import PlattCertificates.Count131072.C060751
import PlattCertificates.Count131072.C060752
import PlattCertificates.Count131072.C060753
import PlattCertificates.Count131072.C060754
import PlattCertificates.Count131072.C060755
import PlattCertificates.Count131072.C060756
import PlattCertificates.Count131072.C060757
import PlattCertificates.Count131072.C060758
import PlattCertificates.Count131072.C060759
import PlattCertificates.Count131072.C060760
import PlattCertificates.Count131072.C060761
import PlattCertificates.Count131072.C060762
import PlattCertificates.Count131072.C060763
import PlattCertificates.Count131072.C060764
import PlattCertificates.Count131072.C060765
import PlattCertificates.Count131072.C060766
import PlattCertificates.Count131072.C060767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60736 : List PrefixCut := [⟨38,119343305,119343376⟩,
⟨64,202108981,202109101⟩]
theorem checked60736 : checkPrefixCuts (2^48) 7964721153 10 Manual.Count131072.C060736.packed 64 cuts60736 = true := by
 decide +kernel
def pointBounds60736 : List (Nat × Nat × Nat) := [(7964798976,114067409985324,114067798478652)]
theorem point_links_checked60736 : (cuts60736.take 1).map (fun c => (7964721153-1+2*2^10*c.k,114067290642019+c.lower,114067679135276+c.upper)) = pointBounds60736 := by
 decide +kernel
def cuts60737 : List PrefixCut := [⟨64,205816291,205816409⟩]
theorem checked60737 : checkPrefixCuts (2^48) 7964852225 10 Manual.Count131072.C060737.packed 64 cuts60737 = true := by
 decide +kernel
def cuts60738 : List PrefixCut := [⟨32,100185777,100185836⟩,
⟨64,202667740,202667854⟩]
theorem checked60738 : checkPrefixCuts (2^48) 7964983297 10 Manual.Count131072.C060738.packed 64 cuts60738 = true := by
 decide +kernel
def pointBounds60738 : List (Nat × Nat × Nat) := [(7965048832,114067798753068,114068187246622)]
theorem point_links_checked60738 : (cuts60738.take 1).map (fun c => (7964983297-1+2*2^10*c.k,114067698567291+c.lower,114068087060786+c.upper)) = pointBounds60738 := by
 decide +kernel
def cuts60739 : List PrefixCut := [⟨64,199413286,199413401⟩]
theorem checked60739 : checkPrefixCuts (2^48) 7965114369 10 Manual.Count131072.C060739.packed 64 cuts60739 = true := by
 decide +kernel
def cuts60740 : List PrefixCut := [⟨26,82372333,82372378⟩,
⟨64,203968574,203968690⟩]
theorem checked60740 : checkPrefixCuts (2^48) 7965245441 10 Manual.Count131072.C060740.packed 64 cuts60740 = true := by
 decide +kernel
def pointBounds60740 : List (Nat × Nat × Nat) := [(7965298688,114068183020650,114068571514419)]
theorem point_links_checked60740 : (cuts60740.take 1).map (fun c => (7965245441-1+2*2^10*c.k,114068100648317+c.lower,114068489142041+c.upper)) = pointBounds60740 := by
 decide +kernel
def cuts60741 : List PrefixCut := [⟨64,201491629,201491742⟩]
theorem checked60741 : checkPrefixCuts (2^48) 7965376513 10 Manual.Count131072.C060741.packed 64 cuts60741 = true := by
 decide +kernel
def cuts60742 : List PrefixCut := [⟨20,63358574,63358609⟩,
⟨64,200993607,200993721⟩]
theorem checked60742 : checkPrefixCuts (2^48) 7965507585 10 Manual.Count131072.C060742.packed 64 cuts60742 = true := by
 decide +kernel
def pointBounds60742 : List (Nat × Nat × Nat) := [(7965548544,114068569467094,114068957961082)]
theorem point_links_checked60742 : (cuts60742.take 1).map (fun c => (7965507585-1+2*2^10*c.k,114068506108520+c.lower,114068894602473+c.upper)) = pointBounds60742 := by
 decide +kernel
def cuts60743 : List PrefixCut := [⟨64,200848938,200849055⟩]
theorem checked60743 : checkPrefixCuts (2^48) 7965638657 10 Manual.Count131072.C060743.packed 64 cuts60743 = true := by
 decide +kernel
def cuts60744 : List PrefixCut := [⟨14,44310707,44310734⟩,
⟨64,203213104,203213215⟩]
theorem checked60744 : checkPrefixCuts (2^48) 7965769729 10 Manual.Count131072.C060744.packed 64 cuts60744 = true := by
 decide +kernel
def pointBounds60744 : List (Nat × Nat × Nat) := [(7965798400,114068952261772,114069340755983)]
theorem point_links_checked60744 : (cuts60744.take 1).map (fun c => (7965769729-1+2*2^10*c.k,114068907951065+c.lower,114069296445249+c.upper)) = pointBounds60744 := by
 decide +kernel
def cuts60745 : List PrefixCut := [⟨64,205859867,205859984⟩]
theorem checked60745 : checkPrefixCuts (2^48) 7965900801 10 Manual.Count131072.C060745.packed 64 cuts60745 = true := by
 decide +kernel
def cuts60746 : List PrefixCut := [⟨8,24345371,24345386⟩,
⟨64,202181713,202181832⟩]
theorem checked60746 : checkPrefixCuts (2^48) 7966031873 10 Manual.Count131072.C060746.packed 64 cuts60746 = true := by
 decide +kernel
def pointBounds60746 : List (Nat × Nat × Nat) := [(7966048256,114069341369407,114069729863834)]
theorem point_links_checked60746 : (cuts60746.take 1).map (fun c => (7966031873-1+2*2^10*c.k,114069317024036+c.lower,114069705518448+c.upper)) = pointBounds60746 := by
 decide +kernel
def cuts60747 : List PrefixCut := [⟨64,201789734,201789848⟩]
theorem checked60747 : checkPrefixCuts (2^48) 7966162945 10 Manual.Count131072.C060747.packed 64 cuts60747 = true := by
 decide +kernel
def cuts60748 : List PrefixCut := [⟨2,6395313,6395317⟩,
⟨64,204047714,204047833⟩]
theorem checked60748 : checkPrefixCuts (2^48) 7966294017 10 Manual.Count131072.C060748.packed 64 cuts60748 = true := by
 decide +kernel
def pointBounds60748 : List (Nat × Nat × Nat) := [(7966298112,114069727390796,114070115885445)]
theorem point_links_checked60748 : (cuts60748.take 1).map (fun c => (7966294017-1+2*2^10*c.k,114069720995483+c.lower,114070109490128+c.upper)) = pointBounds60748 := by
 decide +kernel
def cuts60749 : List PrefixCut := [⟨60,192667440,192667549⟩,
⟨64,204821677,204821794⟩]
theorem checked60749 : checkPrefixCuts (2^48) 7966425089 10 Manual.Count131072.C060749.packed 64 cuts60749 = true := by
 decide +kernel
def pointBounds60749 : List (Nat × Nat × Nat) := [(7966547968,114070117710637,114070506205510)]
theorem point_links_checked60749 : (cuts60749.take 1).map (fun c => (7966425089-1+2*2^10*c.k,114069925043197+c.lower,114070313537961+c.upper)) = pointBounds60749 := by
 decide +kernel
def cuts60750 : List PrefixCut := [⟨64,201991762,201991882⟩]
theorem checked60750 : checkPrefixCuts (2^48) 7966556161 10 Manual.Count131072.C060750.packed 64 cuts60750 = true := by
 decide +kernel
def cuts60751 : List PrefixCut := [⟨54,171073858,171073956⟩,
⟨64,202200425,202200541⟩]
theorem checked60751 : checkPrefixCuts (2^48) 7966687233 10 Manual.Count131072.C060751.packed 64 cuts60751 = true := by
 decide +kernel
def pointBounds60751 : List (Nat × Nat × Nat) := [(7966797824,114070502930494,114070891425593)]
theorem point_links_checked60751 : (cuts60751.take 1).map (fun c => (7966687233-1+2*2^10*c.k,114070331856636+c.lower,114070720351637+c.upper)) = pointBounds60751 := by
 decide +kernel
def cuts60752 : List PrefixCut := [⟨64,205482866,205482986⟩]
theorem checked60752 : checkPrefixCuts (2^48) 7966818305 10 Manual.Count131072.C060752.packed 64 cuts60752 = true := by
 decide +kernel
def cuts60753 : List PrefixCut := [⟨48,150400255,150400344⟩,
⟨64,200533261,200533381⟩]
theorem checked60753 : checkPrefixCuts (2^48) 7966949377 10 Manual.Count131072.C060753.packed 64 cuts60753 = true := by
 decide +kernel
def pointBounds60753 : List (Nat × Nat × Nat) := [(7967047680,114070889940182,114071278435508)]
theorem point_links_checked60753 : (cuts60753.take 1).map (fun c => (7966949377-1+2*2^10*c.k,114070739539927+c.lower,114071128035164+c.upper)) = pointBounds60753 := by
 decide +kernel
def cuts60754 : List PrefixCut := [⟨64,205228784,205228900⟩]
theorem checked60754 : checkPrefixCuts (2^48) 7967080449 10 Manual.Count131072.C060754.packed 64 cuts60754 = true := by
 decide +kernel
def cuts60755 : List PrefixCut := [⟨42,133790809,133790885⟩,
⟨64,202681734,202681850⟩]
theorem checked60755 : checkPrefixCuts (2^48) 7967211521 10 Manual.Count131072.C060755.packed 64 cuts60755 = true := by
 decide +kernel
def pointBounds60755 : List (Nat × Nat × Nat) := [(7967297536,114071279092781,114071667588330)]
theorem point_links_checked60755 : (cuts60755.take 1).map (fun c => (7967211521-1+2*2^10*c.k,114071145301972+c.lower,114071533797445+c.upper)) = pointBounds60755 := by
 decide +kernel
def cuts60756 : List PrefixCut := [⟨64,203384966,203385076⟩]
theorem checked60756 : checkPrefixCuts (2^48) 7967342593 10 Manual.Count131072.C060756.packed 64 cuts60756 = true := by
 decide +kernel
def cuts60757 : List PrefixCut := [⟨36,111812602,111812668⟩,
⟨64,202321772,202321891⟩]
theorem checked60757 : checkPrefixCuts (2^48) 7967473665 10 Manual.Count131072.C060757.packed 64 cuts60757 = true := by
 decide +kernel
def pointBounds60757 : List (Nat × Nat × Nat) := [(7967547392,114071663181274,114072051677039)]
theorem point_links_checked60757 : (cuts60757.take 1).map (fun c => (7967473665-1+2*2^10*c.k,114071551368672+c.lower,114071939864371+c.upper)) = pointBounds60757 := by
 decide +kernel
def cuts60758 : List PrefixCut := [⟨64,200905379,200905491⟩]
theorem checked60758 : checkPrefixCuts (2^48) 7967604737 10 Manual.Count131072.C060758.packed 64 cuts60758 = true := by
 decide +kernel
def cuts60759 : List PrefixCut := [⟨30,95099474,95099529⟩,
⟨64,204646669,204646784⟩]
theorem checked60759 : checkPrefixCuts (2^48) 7967735809 10 Manual.Count131072.C060759.packed 64 cuts60759 = true := by
 decide +kernel
def pointBounds60759 : List (Nat × Nat × Nat) := [(7967797248,114072049695297,114072438191282)]
theorem point_links_checked60759 : (cuts60759.take 1).map (fun c => (7967735809-1+2*2^10*c.k,114071954595823+c.lower,114072343091753+c.upper)) = pointBounds60759 := by
 decide +kernel
def cuts60760 : List PrefixCut := [⟨64,201393314,201393428⟩]
theorem checked60760 : checkPrefixCuts (2^48) 7967866881 10 Manual.Count131072.C060760.packed 64 cuts60760 = true := by
 decide +kernel
def cuts60761 : List PrefixCut := [⟨24,74890196,74890242⟩,
⟨64,200365568,200365684⟩]
theorem checked60761 : checkPrefixCuts (2^48) 7967997953 10 Manual.Count131072.C060761.packed 64 cuts60761 = true := by
 decide +kernel
def pointBounds60761 : List (Nat × Nat × Nat) := [(7968047104,114072435526002,114072824022207)]
theorem point_links_checked60761 : (cuts60761.take 1).map (fun c => (7967997953-1+2*2^10*c.k,114072360635806+c.lower,114072749131965+c.upper)) = pointBounds60761 := by
 decide +kernel
def cuts60762 : List PrefixCut := [⟨64,204848525,204848644⟩]
theorem checked60762 : checkPrefixCuts (2^48) 7968129025 10 Manual.Count131072.C060762.packed 64 cuts60762 = true := by
 decide +kernel
def cuts60763 : List PrefixCut := [⟨18,57260902,57260934⟩,
⟨64,203750111,203750226⟩]
theorem checked60763 : checkPrefixCuts (2^48) 7968260097 10 Manual.Count131072.C060763.packed 64 cuts60763 = true := by
 decide +kernel
def pointBounds60763 : List (Nat × Nat × Nat) := [(7968296960,114072823110801,114073211607227)]
theorem point_links_checked60763 : (cuts60763.take 1).map (fun c => (7968260097-1+2*2^10*c.k,114072765849899+c.lower,114073154346293+c.upper)) = pointBounds60763 := by
 decide +kernel
def cuts60764 : List PrefixCut := [⟨64,203570139,203570253⟩]
theorem checked60764 : checkPrefixCuts (2^48) 7968391169 10 Manual.Count131072.C060764.packed 64 cuts60764 = true := by
 decide +kernel
def cuts60765 : List PrefixCut := [⟨12,39774030,39774053⟩,
⟨64,205050361,205050482⟩]
theorem checked60765 : checkPrefixCuts (2^48) 7968522241 10 Manual.Count131072.C060765.packed 64 cuts60765 = true := by
 decide +kernel
def pointBounds60765 : List (Nat × Nat × Nat) := [(7968546816,114073212944179,114073601440825)]
theorem point_links_checked60765 : (cuts60765.take 1).map (fun c => (7968522241-1+2*2^10*c.k,114073173170149+c.lower,114073561666772+c.upper)) = pointBounds60765 := by
 decide +kernel
def cuts60766 : List PrefixCut := [⟨64,202751031,202751150⟩]
theorem checked60766 : checkPrefixCuts (2^48) 7968653313 10 Manual.Count131072.C060766.packed 64 cuts60766 = true := by
 decide +kernel
def cuts60767 : List PrefixCut := [⟨6,18967999,18968010⟩,
⟨64,200204509,200204623⟩]
theorem checked60767 : checkPrefixCuts (2^48) 7968784385 10 Manual.Count131072.C060767.packed 64 cuts60767 = true := by
 decide +kernel
def pointBounds60767 : List (Nat × Nat × Nat) := [(7968796672,114073599939540,114073988436414)]
theorem point_links_checked60767 : (cuts60767.take 1).map (fun c => (7968784385-1+2*2^10*c.k,114073580971541+c.lower,114073969468404+c.upper)) = pointBounds60767 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000023
