import PlattAssemblyKernel
import PlattCertificates.Count131072.C025632
import PlattCertificates.Count131072.C025633
import PlattCertificates.Count131072.C025634
import PlattCertificates.Count131072.C025635
import PlattCertificates.Count131072.C025636
import PlattCertificates.Count131072.C025637
import PlattCertificates.Count131072.C025638
import PlattCertificates.Count131072.C025639
import PlattCertificates.Count131072.C025640
import PlattCertificates.Count131072.C025641
import PlattCertificates.Count131072.C025642
import PlattCertificates.Count131072.C025643
import PlattCertificates.Count131072.C025644
import PlattCertificates.Count131072.C025645
import PlattCertificates.Count131072.C025646
import PlattCertificates.Count131072.C025647
import PlattCertificates.Count131072.C025648
import PlattCertificates.Count131072.C025649
import PlattCertificates.Count131072.C025650
import PlattCertificates.Count131072.C025651
import PlattCertificates.Count131072.C025652
import PlattCertificates.Count131072.C025653
import PlattCertificates.Count131072.C025654
import PlattCertificates.Count131072.C025655
import PlattCertificates.Count131072.C025656
import PlattCertificates.Count131072.C025657
import PlattCertificates.Count131072.C025658
import PlattCertificates.Count131072.C025659
import PlattCertificates.Count131072.C025660
import PlattCertificates.Count131072.C025661
import PlattCertificates.Count131072.C025662
import PlattCertificates.Count131072.C025663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000176
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25632 : List PrefixCut := [⟨75,289457529,289457689⟩,
⟨128,495228614,495228887⟩]
theorem checked25632 : checkPrefixCuts (2^48) 3363569665 9 Manual.Count131072.C025632.packed 128 cuts25632 = true := by
 decide +kernel
def pointBounds25632 : List (Nat × Nat × Nat) := [(3363646464,103218442600326,103218824796393)]
theorem point_links_checked25632 : (cuts25632.take 1).map (fun c => (3363569665-1+2*2^9*c.k,103218153142797+c.lower,103218535338704+c.upper)) = pointBounds25632 := by
 decide +kernel
def cuts25633 : List PrefixCut := [⟨50,193466981,193467092⟩,
⟨128,497719701,497719980⟩]
theorem checked25633 : checkPrefixCuts (2^48) 3363700737 9 Manual.Count131072.C025633.packed 128 cuts25633 = true := by
 decide +kernel
def pointBounds25633 : List (Nat × Nat × Nat) := [(3363751936,103218841838392,103219224034683)]
theorem point_links_checked25633 : (cuts25633.take 1).map (fun c => (3363700737-1+2*2^9*c.k,103218648371411+c.lower,103219030567591+c.upper)) = pointBounds25633 := by
 decide +kernel
def cuts25634 : List PrefixCut := [⟨25,99073033,99073086⟩,
⟨128,499624834,499625112⟩]
theorem checked25634 : checkPrefixCuts (2^48) 3363831809 9 Manual.Count131072.C025634.packed 128 cuts25634 = true := by
 decide +kernel
def pointBounds25634 : List (Nat × Nat × Nat) := [(3363857408,103219245164145,103219627360657),(3363962880,103219645715946,103220027912683)]
theorem point_links_checked25634 : (cuts25634.take 2).map (fun c => (3363831809-1+2*2^9*c.k,103219146091112+c.lower,103219528287571+c.upper)) = pointBounds25634 := by
 decide +kernel
def cuts25635 : List PrefixCut := [⟨103,392925106,392925323⟩,
⟨128,488644336,488644609⟩]
theorem checked25635 : checkPrefixCuts (2^48) 3363962881 9 Manual.Count131072.C025635.packed 128 cuts25635 = true := by
 decide +kernel
def pointBounds25635 : List (Nat × Nat × Nat) := [(3364068352,103220038641052,103220420838006)]
theorem point_links_checked25635 : (cuts25635.take 1).map (fun c => (3363962881-1+2*2^9*c.k,103219645715946+c.lower,103220027912683+c.upper)) = pointBounds25635 := by
 decide +kernel
def cuts25636 : List PrefixCut := [⟨78,310078636,310078806⟩,
⟨128,503769425,503769706⟩]
theorem checked25636 : checkPrefixCuts (2^48) 3364093953 9 Manual.Count131072.C025636.packed 128 cuts25636 = true := by
 decide +kernel
def pointBounds25636 : List (Nat × Nat × Nat) := [(3364173824,103220444438918,103220826636098)]
theorem point_links_checked25636 : (cuts25636.take 1).map (fun c => (3364093953-1+2*2^9*c.k,103220134360282+c.lower,103220516557292+c.upper)) = pointBounds25636 := by
 decide +kernel
def cuts25637 : List PrefixCut := [⟨53,208998706,208998821⟩,
⟨128,503080397,503080678⟩]
theorem checked25637 : checkPrefixCuts (2^48) 3364225025 9 Manual.Count131072.C025637.packed 128 cuts25637 = true := by
 decide +kernel
def pointBounds25637 : List (Nat × Nat × Nat) := [(3364279296,103220847128413,103221229325819)]
theorem point_links_checked25637 : (cuts25637.take 1).map (fun c => (3364225025-1+2*2^9*c.k,103220638129707+c.lower,103221020326998+c.upper)) = pointBounds25637 := by
 decide +kernel
def cuts25638 : List PrefixCut := [⟨28,108344188,108344250⟩,
⟨128,499128650,499128938⟩]
theorem checked25638 : checkPrefixCuts (2^48) 3364356097 9 Manual.Count131072.C025638.packed 128 cuts25638 = true := by
 decide +kernel
def pointBounds25638 : List (Nat × Nat × Nat) := [(3364384768,103221249554292,103221631751926)]
theorem point_links_checked25638 : (cuts25638.take 1).map (fun c => (3364356097-1+2*2^9*c.k,103221141210104+c.lower,103221523407676+c.upper)) = pointBounds25638 := by
 decide +kernel
def cuts25639 : List PrefixCut := [⟨3,10959529,10959535⟩,
⟨106,409679162,409679394⟩,
⟨128,494256975,494257258⟩]
theorem checked25639 : checkPrefixCuts (2^48) 3364487169 9 Manual.Count131072.C025639.packed 128 cuts25639 = true := by
 decide +kernel
def pointBounds25639 : List (Nat × Nat × Nat) := [(3364490240,103221651298283,103222033496149),(3364595712,103222050017916,103222432216008)]
theorem point_links_checked25639 : (cuts25639.take 2).map (fun c => (3364487169-1+2*2^9*c.k,103221640338754+c.lower,103222022536614+c.upper)) = pointBounds25639 := by
 decide +kernel
def cuts25640 : List PrefixCut := [⟨81,318730373,318730551⟩,
⟨128,503523496,503523776⟩]
theorem checked25640 : checkPrefixCuts (2^48) 3364618241 9 Manual.Count131072.C025640.packed 128 cuts25640 = true := by
 decide +kernel
def pointBounds25640 : List (Nat × Nat × Nat) := [(3364701184,103222453326102,103222835524423)]
theorem point_links_checked25640 : (cuts25640.take 1).map (fun c => (3364618241-1+2*2^9*c.k,103222134595729+c.lower,103222516793872+c.upper)) = pointBounds25640 := by
 decide +kernel
def cuts25641 : List PrefixCut := [⟨56,221263085,221263206⟩,
⟨128,494134987,494135265⟩]
theorem checked25641 : checkPrefixCuts (2^48) 3364749313 9 Manual.Count131072.C025641.packed 128 cuts25641 = true := by
 decide +kernel
def pointBounds25641 : List (Nat × Nat × Nat) := [(3364806656,103222859382310,103223241580854)]
theorem point_links_checked25641 : (cuts25641.take 1).map (fun c => (3364749313-1+2*2^9*c.k,103222638119225+c.lower,103223020317648+c.upper)) = pointBounds25641 := by
 decide +kernel
def cuts25642 : List PrefixCut := [⟨31,120289257,120289325⟩,
⟨128,503735186,503735461⟩]
theorem checked25642 : checkPrefixCuts (2^48) 3364880385 9 Manual.Count131072.C025642.packed 128 cuts25642 = true := by
 decide +kernel
def pointBounds25642 : List (Nat × Nat × Nat) := [(3364912128,103223252543469,103223634742238)]
theorem point_links_checked25642 : (cuts25642.take 1).map (fun c => (3364880385-1+2*2^9*c.k,103223132254212+c.lower,103223514452913+c.upper)) = pointBounds25642 := by
 decide +kernel
def cuts25643 : List PrefixCut := [⟨6,23170345,23170358⟩,
⟨109,429439324,429439564⟩,
⟨128,501122671,501122952⟩]
theorem checked25643 : checkPrefixCuts (2^48) 3365011457 9 Manual.Count131072.C025643.packed 128 cuts25643 = true := by
 decide +kernel
def pointBounds25643 : List (Nat × Nat × Nat) := [(3365017600,103223659159743,103224041358732),(3365123072,103224065428722,103224447627938)]
theorem point_links_checked25643 : (cuts25643.take 2).map (fun c => (3365011457-1+2*2^9*c.k,103223635989398+c.lower,103224018188374+c.upper)) = pointBounds25643 := by
 decide +kernel
def cuts25644 : List PrefixCut := [⟨84,328215966,328216145⟩,
⟨128,501772232,501772510⟩]
theorem checked25644 : checkPrefixCuts (2^48) 3365142529 9 Manual.Count131072.C025644.packed 128 cuts25644 = true := by
 decide +kernel
def pointBounds25644 : List (Nat × Nat × Nat) := [(3365228544,103224465328035,103224847527471)]
theorem point_links_checked25644 : (cuts25644.take 1).map (fun c => (3365142529-1+2*2^9*c.k,103224137112069+c.lower,103224519311326+c.upper)) = pointBounds25644 := by
 decide +kernel
def cuts25645 : List PrefixCut := [⟨59,230763485,230763613⟩,
⟨128,501083582,501083858⟩]
theorem checked25645 : checkPrefixCuts (2^48) 3365273601 9 Manual.Count131072.C025645.packed 128 cuts25645 = true := by
 decide +kernel
def pointBounds25645 : List (Nat × Nat × Nat) := [(3365334016,103224869647786,103225251847449)]
theorem point_links_checked25645 : (cuts25645.take 1).map (fun c => (3365273601-1+2*2^9*c.k,103224638884301+c.lower,103225021083836+c.upper)) = pointBounds25645 := by
 decide +kernel
def cuts25646 : List PrefixCut := [⟨34,130557854,130557928⟩,
⟨128,494874948,494875226⟩]
theorem checked25646 : checkPrefixCuts (2^48) 3365404673 9 Manual.Count131072.C025646.packed 128 cuts25646 = true := by
 decide +kernel
def pointBounds25646 : List (Nat × Nat × Nat) := [(3365439488,103225270525737,103225652725622)]
theorem point_links_checked25646 : (cuts25646.take 1).map (fun c => (3365404673-1+2*2^9*c.k,103225139967883+c.lower,103225522167694+c.upper)) = pointBounds25646 := by
 decide +kernel
def cuts25647 : List PrefixCut := [⟨9,35879152,35879172⟩,
⟨112,434473852,434474098⟩,
⟨128,497531964,497532243⟩]
theorem checked25647 : checkPrefixCuts (2^48) 3365535745 9 Manual.Count131072.C025647.packed 128 cuts25647 = true := by
 decide +kernel
def pointBounds25647 : List (Nat × Nat × Nat) := [(3365544960,103225670721983,103226052922092),(3365650432,103226069316683,103226451517018)]
theorem point_links_checked25647 : (cuts25647.take 2).map (fun c => (3365535745-1+2*2^9*c.k,103225634842831+c.lower,103226017042920+c.upper)) = pointBounds25647 := by
 decide +kernel
def cuts25648 : List PrefixCut := [⟨87,335440509,335440694⟩,
⟨128,496759910,496760185⟩]
theorem checked25648 : checkPrefixCuts (2^48) 3365666817 9 Manual.Count131072.C025648.packed 128 cuts25648 = true := by
 decide +kernel
def pointBounds25648 : List (Nat × Nat × Nat) := [(3365755904,103226467815304,103226850015857)]
theorem point_links_checked25648 : (cuts25648.take 1).map (fun c => (3365666817-1+2*2^9*c.k,103226132374795+c.lower,103226514575163+c.upper)) = pointBounds25648 := by
 decide +kernel
def cuts25649 : List PrefixCut := [⟨62,243187937,243188071⟩,
⟨128,495235380,495235656⟩]
theorem checked25649 : checkPrefixCuts (2^48) 3365797889 9 Manual.Count131072.C025649.packed 128 cuts25649 = true := by
 decide +kernel
def pointBounds25649 : List (Nat × Nat × Nat) := [(3365861376,103226872322642,103227254523419)]
theorem point_links_checked25649 : (cuts25649.take 1).map (fun c => (3365797889-1+2*2^9*c.k,103226629134705+c.lower,103227011335348+c.upper)) = pointBounds25649 := by
 decide +kernel
def cuts25650 : List PrefixCut := [⟨37,143415600,143415683⟩,
⟨128,500066108,500066394⟩]
theorem checked25650 : checkPrefixCuts (2^48) 3365928961 9 Manual.Count131072.C025650.packed 128 cuts25650 = true := by
 decide +kernel
def pointBounds25650 : List (Nat × Nat × Nat) := [(3365966848,103227267785685,103227649986687)]
theorem point_links_checked25650 : (cuts25650.take 1).map (fun c => (3365928961-1+2*2^9*c.k,103227124370085+c.lower,103227506571004+c.upper)) = pointBounds25650 := by
 decide +kernel
def cuts25651 : List PrefixCut := [⟨12,47580530,47580557⟩,
⟨115,449708427,449708674⟩,
⟨128,501802678,501802954⟩]
theorem checked25651 : checkPrefixCuts (2^48) 3366060033 9 Manual.Count131072.C025651.packed 128 cuts25651 = true := by
 decide +kernel
def pointBounds25651 : List (Nat × Nat × Nat) := [(3366072320,103227672016723,103228054217955),(3366177792,103228074144620,103228456346072)]
theorem point_links_checked25651 : (cuts25651.take 2).map (fun c => (3366060033-1+2*2^9*c.k,103227624436193+c.lower,103228006637398+c.upper)) = pointBounds25651 := by
 decide +kernel
def cuts25652 : List PrefixCut := [⟨90,347596185,347596379⟩,
⟨128,494842983,494843261⟩]
theorem checked25652 : checkPrefixCuts (2^48) 3366191105 9 Manual.Count131072.C025652.packed 128 cuts25652 = true := by
 decide +kernel
def pointBounds25652 : List (Nat × Nat × Nat) := [(3366283264,103228473835056,103228856036731)]
theorem point_links_checked25652 : (cuts25652.take 1).map (fun c => (3366191105-1+2*2^9*c.k,103228126238871+c.lower,103228508440352+c.upper)) = pointBounds25652 := by
 decide +kernel
def cuts25653 : List PrefixCut := [⟨65,249253736,249253876⟩,
⟨128,501847095,501847373⟩]
theorem checked25653 : checkPrefixCuts (2^48) 3366322177 9 Manual.Count131072.C025653.packed 128 cuts25653 = true := by
 decide +kernel
def pointBounds25653 : List (Nat × Nat × Nat) := [(3366388736,103228870335590,103229252537489)]
theorem point_links_checked25653 : (cuts25653.take 1).map (fun c => (3366322177-1+2*2^9*c.k,103228621081854+c.lower,103229003283613+c.upper)) = pointBounds25653 := by
 decide +kernel
def cuts25654 : List PrefixCut := [⟨40,156018480,156018567⟩,
⟨128,502663771,502664044⟩]
theorem checked25654 : checkPrefixCuts (2^48) 3366453249 9 Manual.Count131072.C025654.packed 128 cuts25654 = true := by
 decide +kernel
def pointBounds25654 : List (Nat × Nat × Nat) := [(3366494208,103229278947429,103229661149553)]
theorem point_links_checked25654 : (cuts25654.take 1).map (fun c => (3366453249-1+2*2^9*c.k,103229122928949+c.lower,103229505130986+c.upper)) = pointBounds25654 := by
 decide +kernel
def cuts25655 : List PrefixCut := [⟨15,57271656,57271688⟩,
⟨118,460256222,460256485⟩,
⟨128,498714669,498714955⟩]
theorem checked25655 : checkPrefixCuts (2^48) 3366584321 9 Manual.Count131072.C025655.packed 128 cuts25655 = true := by
 decide +kernel
def pointBounds25655 : List (Nat × Nat × Nat) := [(3366599680,103229682864376,103230065066718),(3366705152,103230085848942,103230468051515)]
theorem point_links_checked25655 : (cuts25655.take 2).map (fun c => (3366584321-1+2*2^9*c.k,103229625592720+c.lower,103230007795030+c.upper)) = pointBounds25655 := by
 decide +kernel
def cuts25656 : List PrefixCut := [⟨93,369613356,369613563⟩,
⟨128,504547604,504547888⟩]
theorem checked25656 : checkPrefixCuts (2^48) 3366715393 9 Manual.Count131072.C025656.packed 128 cuts25656 = true := by
 decide +kernel
def pointBounds25656 : List (Nat × Nat × Nat) := [(3366810624,103230493920745,103230876123548)]
theorem point_links_checked25656 : (cuts25656.take 1).map (fun c => (3366715393-1+2*2^9*c.k,103230124307389+c.lower,103230506509985+c.upper)) = pointBounds25656 := by
 decide +kernel
def cuts25657 : List PrefixCut := [⟨68,265684218,265684371⟩,
⟨128,500180673,500180956⟩]
theorem checked25657 : checkPrefixCuts (2^48) 3366846465 9 Manual.Count131072.C025657.packed 128 cuts25657 = true := by
 decide +kernel
def pointBounds25657 : List (Nat × Nat × Nat) := [(3366916096,103230894539211,103231276742244)]
theorem point_links_checked25657 : (cuts25657.take 1).map (fun c => (3366846465-1+2*2^9*c.k,103230628854993+c.lower,103231011057873+c.upper)) = pointBounds25657 := by
 decide +kernel
def cuts25658 : List PrefixCut := [⟨43,169369831,169369925⟩,
⟨128,501080760,501081041⟩]
theorem checked25658 : checkPrefixCuts (2^48) 3366977537 9 Manual.Count131072.C025658.packed 128 cuts25658 = true := by
 decide +kernel
def pointBounds25658 : List (Nat × Nat × Nat) := [(3367021568,103231298405497,103231680608754)]
theorem point_links_checked25658 : (cuts25658.take 1).map (fun c => (3366977537-1+2*2^9*c.k,103231129035666+c.lower,103231511238829+c.upper)) = pointBounds25658 := by
 decide +kernel
def cuts25659 : List PrefixCut := [⟨18,67712118,67712153⟩,
⟨121,466035980,466036244⟩,
⟨128,492785504,492785784⟩]
theorem checked25659 : checkPrefixCuts (2^48) 3367108609 9 Manual.Count131072.C025659.packed 128 cuts25659 = true := by
 decide +kernel
def pointBounds25659 : List (Nat × Nat × Nat) := [(3367127040,103231697828544,103232080032023),(3367232512,103232096152406,103232478356114)]
theorem point_links_checked25659 : (cuts25659.take 2).map (fun c => (3367108609-1+2*2^9*c.k,103231630116426+c.lower,103232012319870+c.upper)) = pointBounds25659 := by
 decide +kernel
def cuts25660 : List PrefixCut := [⟨96,371896196,371896409⟩,
⟨128,498032488,498032776⟩]
theorem checked25660 : checkPrefixCuts (2^48) 3367239681 9 Manual.Count131072.C025660.packed 128 cuts25660 = true := by
 decide +kernel
def pointBounds25660 : List (Nat × Nat × Nat) := [(3367337984,103232494798126,103232877002063)]
theorem point_links_checked25660 : (cuts25660.take 1).map (fun c => (3367239681-1+2*2^9*c.k,103232122901930+c.lower,103232505105654+c.upper)) = pointBounds25660 := by
 decide +kernel
def cuts25661 : List PrefixCut := [⟨71,281273684,281273836⟩,
⟨128,503864250,503864527⟩]
theorem checked25661 : checkPrefixCuts (2^48) 3367370753 9 Manual.Count131072.C025661.packed 128 cuts25661 = true := by
 decide +kernel
def pointBounds25661 : List (Nat × Nat × Nat) := [(3367443456,103232902208102,103233284412266)]
theorem point_links_checked25661 : (cuts25661.take 1).map (fun c => (3367370753-1+2*2^9*c.k,103232620934418+c.lower,103233003138430+c.upper)) = pointBounds25661 := by
 decide +kernel
def cuts25662 : List PrefixCut := [⟨46,178872078,178872180⟩,
⟨128,503175876,503176156⟩]
theorem checked25662 : checkPrefixCuts (2^48) 3367501825 9 Manual.Count131072.C025662.packed 128 cuts25662 = true := by
 decide +kernel
def pointBounds25662 : List (Nat × Nat × Nat) := [(3367548928,103233303670746,103233685875137)]
theorem point_links_checked25662 : (cuts25662.take 1).map (fun c => (3367501825-1+2*2^9*c.k,103233124798668+c.lower,103233507002957+c.upper)) = pointBounds25662 := by
 decide +kernel
def cuts25663 : List PrefixCut := [⟨21,81492596,81492643⟩,
⟨124,481927116,481927387⟩,
⟨128,498893698,498893978⟩]
theorem checked25663 : checkPrefixCuts (2^48) 3367632897 9 Manual.Count131072.C025663.packed 128 cuts25663 = true := by
 decide +kernel
def pointBounds25663 : List (Nat × Nat × Nat) := [(3367654400,103233709467140,103234091671756),(3367759872,103234109901660,103234492106500)]
theorem point_links_checked25663 : (cuts25663.take 2).map (fun c => (3367632897-1+2*2^9*c.k,103233627974544+c.lower,103234010179113+c.upper)) = pointBounds25663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000176
