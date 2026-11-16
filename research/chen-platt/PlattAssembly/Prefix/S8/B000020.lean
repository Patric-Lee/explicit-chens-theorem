import PlattAssemblyKernel
import PlattCertificates.Count131072.C070640
import PlattCertificates.Count131072.C070641
import PlattCertificates.Count131072.C070642
import PlattCertificates.Count131072.C070643
import PlattCertificates.Count131072.C070644
import PlattCertificates.Count131072.C070645
import PlattCertificates.Count131072.C070646
import PlattCertificates.Count131072.C070647
import PlattCertificates.Count131072.C070648
import PlattCertificates.Count131072.C070649
import PlattCertificates.Count131072.C070650
import PlattCertificates.Count131072.C070651
import PlattCertificates.Count131072.C070652
import PlattCertificates.Count131072.C070653
import PlattCertificates.Count131072.C070654
import PlattCertificates.Count131072.C070655
import PlattCertificates.Count131072.C070656
import PlattCertificates.Count131072.C070657
import PlattCertificates.Count131072.C070658
import PlattCertificates.Count131072.C070659
import PlattCertificates.Count131072.C070660
import PlattCertificates.Count131072.C070661
import PlattCertificates.Count131072.C070662
import PlattCertificates.Count131072.C070663
import PlattCertificates.Count131072.C070664
import PlattCertificates.Count131072.C070665
import PlattCertificates.Count131072.C070666
import PlattCertificates.Count131072.C070667
import PlattCertificates.Count131072.C070668
import PlattCertificates.Count131072.C070669
import PlattCertificates.Count131072.C070670
import PlattCertificates.Count131072.C070671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70640 : List PrefixCut := [⟨64,174301327,174301427⟩]
theorem checked70640 : checkPrefixCuts (2^48) 9262858241 10 Manual.Count131072.C070640.packed 64 cuts70640 = true := by
 decide +kernel
def cuts70641 : List PrefixCut := [⟨55,149776845,149776937⟩,
⟨64,174146935,174147042⟩]
theorem checked70641 : checkPrefixCuts (2^48) 9262989313 10 Manual.Count131072.C070641.packed 64 cuts70641 = true := by
 decide +kernel
def pointBounds70641 : List (Nat × Nat × Nat) := [(9263101952,115925676432131,115926066003243)]
theorem point_links_checked70641 : (cuts70641.take 1).map (fun c => (9262989313-1+2*2^10*c.k,115925526655286+c.lower,115925916226306+c.upper)) = pointBounds70641 := by
 decide +kernel
def cuts70642 : List PrefixCut := [⟨64,172199746,172199849⟩]
theorem checked70642 : checkPrefixCuts (2^48) 9263120385 10 Manual.Count131072.C070642.packed 64 cuts70642 = true := by
 decide +kernel
def cuts70643 : List PrefixCut := [⟨64,175175131,175175232⟩]
theorem checked70643 : checkPrefixCuts (2^48) 9263251457 10 Manual.Count131072.C070643.packed 64 cuts70643 = true := by
 decide +kernel
def cuts70644 : List PrefixCut := [⟨5,12974710,12974719⟩,
⟨64,173683758,173683850⟩]
theorem checked70644 : checkPrefixCuts (2^48) 9263382529 10 Manual.Count131072.C070644.packed 64 cuts70644 = true := by
 decide +kernel
def pointBounds70644 : List (Nat × Nat × Nat) := [(9263392768,115926061151808,115926450723148)]
theorem point_links_checked70644 : (cuts70644.take 1).map (fun c => (9263382529-1+2*2^10*c.k,115926048177098+c.lower,115926437748429+c.upper)) = pointBounds70644 := by
 decide +kernel
def cuts70645 : List PrefixCut := [⟨64,175230945,175231047⟩]
theorem checked70645 : checkPrefixCuts (2^48) 9263513601 10 Manual.Count131072.C070645.packed 64 cuts70645 = true := by
 decide +kernel
def cuts70646 : List PrefixCut := [⟨19,51198446,51198476⟩,
⟨64,174772691,174772792⟩]
theorem checked70646 : checkPrefixCuts (2^48) 9263644673 10 Manual.Count131072.C070646.packed 64 cuts70646 = true := by
 decide +kernel
def pointBounds70646 : List (Nat × Nat × Nat) := [(9263683584,115926448290247,115926837861802)]
theorem point_links_checked70646 : (cuts70646.take 1).map (fun c => (9263644673-1+2*2^10*c.k,115926397091801+c.lower,115926786663326+c.upper)) = pointBounds70646 := by
 decide +kernel
def cuts70647 : List PrefixCut := [⟨64,174132155,174132260⟩]
theorem checked70647 : checkPrefixCuts (2^48) 9263775745 10 Manual.Count131072.C070647.packed 64 cuts70647 = true := by
 decide +kernel
def cuts70648 : List PrefixCut := [⟨33,90544105,90544160⟩,
⟨64,173734706,173734813⟩]
theorem checked70648 : checkPrefixCuts (2^48) 9263906817 10 Manual.Count131072.C070648.packed 64 cuts70648 = true := by
 decide +kernel
def pointBounds70648 : List (Nat × Nat × Nat) := [(9263974400,115926836540752,115927226112538)]
theorem point_links_checked70648 : (cuts70648.take 1).map (fun c => (9263906817-1+2*2^10*c.k,115926745996647+c.lower,115927135568378+c.upper)) = pointBounds70648 := by
 decide +kernel
def cuts70649 : List PrefixCut := [⟨64,173884170,173884268⟩]
theorem checked70649 : checkPrefixCuts (2^48) 9264037889 10 Manual.Count131072.C070649.packed 64 cuts70649 = true := by
 decide +kernel
def cuts70650 : List PrefixCut := [⟨47,127456769,127456846⟩,
⟨64,175188158,175188260⟩]
theorem checked70650 : checkPrefixCuts (2^48) 9264168961 10 Manual.Count131072.C070650.packed 64 cuts70650 = true := by
 decide +kernel
def pointBounds70650 : List (Nat × Nat × Nat) := [(9264265216,115927221072292,115927610644305)]
theorem point_links_checked70650 : (cuts70650.take 1).map (fun c => (9264168961-1+2*2^10*c.k,115927093615523+c.lower,115927483187459+c.upper)) = pointBounds70650 := by
 decide +kernel
def cuts70651 : List PrefixCut := [⟨64,174608419,174608523⟩]
theorem checked70651 : checkPrefixCuts (2^48) 9264300033 10 Manual.Count131072.C070651.packed 64 cuts70651 = true := by
 decide +kernel
def cuts70652 : List PrefixCut := [⟨61,167101626,167101721⟩,
⟨64,175669321,175669421⟩]
theorem checked70652 : checkPrefixCuts (2^48) 9264431105 10 Manual.Count131072.C070652.packed 64 cuts70652 = true := by
 decide +kernel
def pointBounds70652 : List (Nat × Nat × Nat) := [(9264556032,115927610513726,115928000085963)]
theorem point_links_checked70652 : (cuts70652.take 1).map (fun c => (9264431105-1+2*2^10*c.k,115927443412100+c.lower,115927832984242+c.upper)) = pointBounds70652 := by
 decide +kernel
def cuts70653 : List PrefixCut := [⟨64,174694624,174694730⟩]
theorem checked70653 : checkPrefixCuts (2^48) 9264562177 10 Manual.Count131072.C070653.packed 64 cuts70653 = true := by
 decide +kernel
def cuts70654 : List PrefixCut := [⟨64,173628807,173628911⟩]
theorem checked70654 : checkPrefixCuts (2^48) 9264693249 10 Manual.Count131072.C070654.packed 64 cuts70654 = true := by
 decide +kernel
def cuts70655 : List PrefixCut := [⟨11,30137944,30137961⟩,
⟨64,173535211,173535311⟩]
theorem checked70655 : checkPrefixCuts (2^48) 9264824321 10 Manual.Count131072.C070655.packed 64 cuts70655 = true := by
 decide +kernel
def pointBounds70655 : List (Nat × Nat × Nat) := [(9264846848,115927997542796,115928387115265)]
theorem point_links_checked70655 : (cuts70655.take 1).map (fun c => (9264824321-1+2*2^10*c.k,115927967404852+c.lower,115928356977304+c.upper)) = pointBounds70655 := by
 decide +kernel
def cuts70656 : List PrefixCut := [⟨64,173866925,173867033⟩]
theorem checked70656 : checkPrefixCuts (2^48) 9264955393 10 Manual.Count131072.C070656.packed 64 cuts70656 = true := by
 decide +kernel
def cuts70657 : List PrefixCut := [⟨25,65620979,65621023⟩,
⟨64,173165716,173165824⟩]
theorem checked70657 : checkPrefixCuts (2^48) 9265086465 10 Manual.Count131072.C070657.packed 64 cuts70657 = true := by
 decide +kernel
def pointBounds70657 : List (Nat × Nat × Nat) := [(9265137664,115928380427967,115928770000671)]
theorem point_links_checked70657 : (cuts70657.take 1).map (fun c => (9265086465-1+2*2^10*c.k,115928314806988+c.lower,115928704379648+c.upper)) = pointBounds70657 := by
 decide +kernel
def cuts70658 : List PrefixCut := [⟨64,174499993,174500094⟩]
theorem checked70658 : checkPrefixCuts (2^48) 9265217537 10 Manual.Count131072.C070658.packed 64 cuts70658 = true := by
 decide +kernel
def cuts70659 : List PrefixCut := [⟨39,107846084,107846145⟩,
⟨64,175348140,175348241⟩]
theorem checked70659 : checkPrefixCuts (2^48) 9265348609 10 Manual.Count131072.C070659.packed 64 cuts70659 = true := by
 decide +kernel
def pointBounds70659 : List (Nat × Nat × Nat) := [(9265428480,115928770318781,115929159891711)]
theorem point_links_checked70659 : (cuts70659.take 1).map (fun c => (9265348609-1+2*2^10*c.k,115928662472697+c.lower,115929052045566+c.upper)) = pointBounds70659 := by
 decide +kernel
def cuts70660 : List PrefixCut := [⟨64,172003994,172004100⟩]
theorem checked70660 : checkPrefixCuts (2^48) 9265479681 10 Manual.Count131072.C070660.packed 64 cuts70660 = true := by
 decide +kernel
def cuts70661 : List PrefixCut := [⟨53,143901871,143901959⟩,
⟨64,174948244,174948351⟩]
theorem checked70661 : checkPrefixCuts (2^48) 9265610753 10 Manual.Count131072.C070661.packed 64 cuts70661 = true := by
 decide +kernel
def pointBounds70661 : List (Nat × Nat × Nat) := [(9265719296,115929153726702,115929543299866)]
theorem point_links_checked70661 : (cuts70661.take 1).map (fun c => (9265610753-1+2*2^10*c.k,115929009824831+c.lower,115929399397907+c.upper)) = pointBounds70661 := by
 decide +kernel
def cuts70662 : List PrefixCut := [⟨64,171543459,171543563⟩]
theorem checked70662 : checkPrefixCuts (2^48) 9265741825 10 Manual.Count131072.C070662.packed 64 cuts70662 = true := by
 decide +kernel
def cuts70663 : List PrefixCut := [⟨64,174973681,174973793⟩]
theorem checked70663 : checkPrefixCuts (2^48) 9265872897 10 Manual.Count131072.C070663.packed 64 cuts70663 = true := by
 decide +kernel
def cuts70664 : List PrefixCut := [⟨3,8687866,8687869⟩,
⟨64,175001594,175001695⟩]
theorem checked70664 : checkPrefixCuts (2^48) 9266003969 10 Manual.Count131072.C070664.packed 64 cuts70664 = true := by
 decide +kernel
def pointBounds70664 : List (Nat × Nat × Nat) := [(9266010112,115929539978081,115929929551483)]
theorem point_links_checked70664 : (cuts70664.take 1).map (fun c => (9266003969-1+2*2^10*c.k,115929531290215+c.lower,115929920863614+c.upper)) = pointBounds70664 := by
 decide +kernel
def cuts70665 : List PrefixCut := [⟨64,173723306,173723409⟩]
theorem checked70665 : checkPrefixCuts (2^48) 9266135041 10 Manual.Count131072.C070665.packed 64 cuts70665 = true := by
 decide +kernel
def cuts70666 : List PrefixCut := [⟨17,44440445,44440474⟩,
⟨64,173052559,173052662⟩]
theorem checked70666 : checkPrefixCuts (2^48) 9266266113 10 Manual.Count131072.C070666.packed 64 cuts70666 = true := by
 decide +kernel
def pointBounds70666 : List (Nat × Nat × Nat) := [(9266300928,115929924455560,115930314029192)]
theorem point_links_checked70666 : (cuts70666.take 1).map (fun c => (9266266113-1+2*2^10*c.k,115929880015115+c.lower,115930269588718+c.upper)) = pointBounds70666 := by
 decide +kernel
def cuts70667 : List PrefixCut := [⟨64,174811922,174812021⟩]
theorem checked70667 : checkPrefixCuts (2^48) 9266397185 10 Manual.Count131072.C070667.packed 64 cuts70667 = true := by
 decide +kernel
def cuts70668 : List PrefixCut := [⟨31,82924671,82924722⟩,
⟨64,173138786,173138892⟩]
theorem checked70668 : checkPrefixCuts (2^48) 9266528257 10 Manual.Count131072.C070668.packed 64 cuts70668 = true := by
 decide +kernel
def pointBounds70668 : List (Nat × Nat × Nat) := [(9266591744,115930310804267,115930700378123)]
theorem point_links_checked70668 : (cuts70668.take 1).map (fun c => (9266528257-1+2*2^10*c.k,115930227879596+c.lower,115930617453401+c.upper)) = pointBounds70668 := by
 decide +kernel
def cuts70669 : List PrefixCut := [⟨64,172650349,172650449⟩]
theorem checked70669 : checkPrefixCuts (2^48) 9266659329 10 Manual.Count131072.C070669.packed 64 cuts70669 = true := by
 decide +kernel
def cuts70670 : List PrefixCut := [⟨45,122226715,122226784⟩,
⟨64,173012405,173012509⟩]
theorem checked70670 : checkPrefixCuts (2^48) 9266790401 10 Manual.Count131072.C070670.packed 64 cuts70670 = true := by
 decide +kernel
def pointBounds70670 : List (Nat × Nat × Nat) := [(9266882560,115930695895446,115931085469526)]
theorem point_links_checked70670 : (cuts70670.take 1).map (fun c => (9266790401-1+2*2^10*c.k,115930573668731+c.lower,115930963242742+c.upper)) = pointBounds70670 := by
 decide +kernel
def cuts70671 : List PrefixCut := [⟨64,177657166,177657269⟩]
theorem checked70671 : checkPrefixCuts (2^48) 9266921473 10 Manual.Count131072.C070671.packed 64 cuts70671 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000020
