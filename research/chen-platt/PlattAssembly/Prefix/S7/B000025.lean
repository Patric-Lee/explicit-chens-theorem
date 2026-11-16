import PlattAssemblyKernel
import PlattCertificates.Count131072.C060800
import PlattCertificates.Count131072.C060801
import PlattCertificates.Count131072.C060802
import PlattCertificates.Count131072.C060803
import PlattCertificates.Count131072.C060804
import PlattCertificates.Count131072.C060805
import PlattCertificates.Count131072.C060806
import PlattCertificates.Count131072.C060807
import PlattCertificates.Count131072.C060808
import PlattCertificates.Count131072.C060809
import PlattCertificates.Count131072.C060810
import PlattCertificates.Count131072.C060811
import PlattCertificates.Count131072.C060812
import PlattCertificates.Count131072.C060813
import PlattCertificates.Count131072.C060814
import PlattCertificates.Count131072.C060815
import PlattCertificates.Count131072.C060816
import PlattCertificates.Count131072.C060817
import PlattCertificates.Count131072.C060818
import PlattCertificates.Count131072.C060819
import PlattCertificates.Count131072.C060820
import PlattCertificates.Count131072.C060821
import PlattCertificates.Count131072.C060822
import PlattCertificates.Count131072.C060823
import PlattCertificates.Count131072.C060824
import PlattCertificates.Count131072.C060825
import PlattCertificates.Count131072.C060826
import PlattCertificates.Count131072.C060827
import PlattCertificates.Count131072.C060828
import PlattCertificates.Count131072.C060829
import PlattCertificates.Count131072.C060830
import PlattCertificates.Count131072.C060831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60800 : List PrefixCut := [⟨64,200872557,200872675⟩]
theorem checked60800 : checkPrefixCuts (2^48) 7973109761 10 Manual.Count131072.C060800.packed 64 cuts60800 = true := by
 decide +kernel
def cuts60801 : List PrefixCut := [⟨26,82713351,82713395⟩,
⟨64,204258264,204258377⟩]
theorem checked60801 : checkPrefixCuts (2^48) 7973240833 10 Manual.Count131072.C060801.packed 64 cuts60801 = true := by
 decide +kernel
def pointBounds60801 : List (Nat × Nat × Nat) := [(7973294080,114080559758679,114080948259518)]
theorem point_links_checked60801 : (cuts60801.take 1).map (fun c => (7973240833-1+2*2^10*c.k,114080477045328+c.lower,114080865546123+c.upper)) = pointBounds60801 := by
 decide +kernel
def cuts60802 : List PrefixCut := [⟨64,203725384,203725502⟩]
theorem checked60802 : checkPrefixCuts (2^48) 7973371905 10 Manual.Count131072.C060802.packed 64 cuts60802 = true := by
 decide +kernel
def cuts60803 : List PrefixCut := [⟨20,63824559,63824595⟩,
⟨64,204286864,204286975⟩]
theorem checked60803 : checkPrefixCuts (2^48) 7973502977 10 Manual.Count131072.C060803.packed 64 cuts60803 = true := by
 decide +kernel
def pointBounds60803 : List (Nat × Nat × Nat) := [(7973543936,114080948853535,114081337354597)]
theorem point_links_checked60803 : (cuts60803.take 1).map (fun c => (7973502977-1+2*2^10*c.k,114080885028976+c.lower,114081273530002+c.upper)) = pointBounds60803 := by
 decide +kernel
def cuts60804 : List PrefixCut := [⟨64,202200778,202200893⟩]
theorem checked60804 : checkPrefixCuts (2^48) 7973634049 10 Manual.Count131072.C060804.packed 64 cuts60804 = true := by
 decide +kernel
def cuts60805 : List PrefixCut := [⟨14,45607677,45607702⟩,
⟨64,205339122,205339235⟩]
theorem checked60805 : checkPrefixCuts (2^48) 7973765121 10 Manual.Count131072.C060805.packed 64 cuts60805 = true := by
 decide +kernel
def pointBounds60805 : List (Nat × Nat × Nat) := [(7973793792,114081337124295,114081725625572)]
theorem point_links_checked60805 : (cuts60805.take 1).map (fun c => (7973765121-1+2*2^10*c.k,114081291516618+c.lower,114081680017870+c.upper)) = pointBounds60805 := by
 decide +kernel
def cuts60806 : List PrefixCut := [⟨64,202582411,202582521⟩]
theorem checked60806 : checkPrefixCuts (2^48) 7973896193 10 Manual.Count131072.C060806.packed 64 cuts60806 = true := by
 decide +kernel
def cuts60807 : List PrefixCut := [⟨8,26685989,26686002⟩,
⟨64,204767615,204767728⟩]
theorem checked60807 : checkPrefixCuts (2^48) 7974027265 10 Manual.Count131072.C060807.packed 64 cuts60807 = true := by
 decide +kernel
def pointBounds60807 : List (Nat × Nat × Nat) := [(7974043648,114081726124140,114082114625628)]
theorem point_links_checked60807 : (cuts60807.take 1).map (fun c => (7974027265-1+2*2^10*c.k,114081699438151+c.lower,114082087939626+c.upper)) = pointBounds60807 := by
 decide +kernel
def cuts60808 : List PrefixCut := [⟨64,201375628,201375742⟩]
theorem checked60808 : checkPrefixCuts (2^48) 7974158337 10 Manual.Count131072.C060808.packed 64 cuts60808 = true := by
 decide +kernel
def cuts60809 : List PrefixCut := [⟨2,6424198,6424202⟩,
⟨64,203454870,203454985⟩]
theorem checked60809 : checkPrefixCuts (2^48) 7974289409 10 Manual.Count131072.C060809.packed 64 cuts60809 = true := by
 decide +kernel
def pointBounds60809 : List (Nat × Nat × Nat) := [(7974293504,114082112005592,114082500507298)]
theorem point_links_checked60809 : (cuts60809.take 1).map (fun c => (7974289409-1+2*2^10*c.k,114082105581394+c.lower,114082494083096+c.upper)) = pointBounds60809 := by
 decide +kernel
def cuts60810 : List PrefixCut := [⟨60,189438715,189438823⟩,
⟨64,202110217,202110332⟩]
theorem checked60810 : checkPrefixCuts (2^48) 7974420481 10 Manual.Count131072.C060810.packed 64 cuts60810 = true := by
 decide +kernel
def pointBounds60810 : List (Nat × Nat × Nat) := [(7974543360,114082498474979,114082886976904)]
theorem point_links_checked60810 : (cuts60810.take 1).map (fun c => (7974420481-1+2*2^10*c.k,114082309036264+c.lower,114082697538081+c.upper)) = pointBounds60810 := by
 decide +kernel
def cuts60811 : List PrefixCut := [⟨64,203412888,203413002⟩]
theorem checked60811 : checkPrefixCuts (2^48) 7974551553 10 Manual.Count131072.C060811.packed 64 cuts60811 = true := by
 decide +kernel
def cuts60812 : List PrefixCut := [⟨54,169772880,169772973⟩,
⟨64,200974124,200974236⟩]
theorem checked60812 : checkPrefixCuts (2^48) 7974682625 10 Manual.Count131072.C060812.packed 64 cuts60812 = true := by
 decide +kernel
def pointBounds60812 : List (Nat × Nat × Nat) := [(7974793216,114082884332249,114083272834388)]
theorem point_links_checked60812 : (cuts60812.take 1).map (fun c => (7974682625-1+2*2^10*c.k,114082714559369+c.lower,114083103061415+c.upper)) = pointBounds60812 := by
 decide +kernel
def cuts60813 : List PrefixCut := [⟨64,203865022,203865139⟩]
theorem checked60813 : checkPrefixCuts (2^48) 7974813697 10 Manual.Count131072.C060813.packed 64 cuts60813 = true := by
 decide +kernel
def cuts60814 : List PrefixCut := [⟨48,153320098,153320189⟩,
⟨64,204532267,204532386⟩]
theorem checked60814 : checkPrefixCuts (2^48) 7974944769 10 Manual.Count131072.C060814.packed 64 cuts60814 = true := by
 decide +kernel
def pointBounds60814 : List (Nat × Nat × Nat) := [(7975043072,114083272718613,114083661220979)]
theorem point_links_checked60814 : (cuts60814.take 1).map (fun c => (7974944769-1+2*2^10*c.k,114083119398515+c.lower,114083507900790+c.upper)) = pointBounds60814 := by
 decide +kernel
def cuts60815 : List PrefixCut := [⟨64,201246566,201246681⟩]
theorem checked60815 : checkPrefixCuts (2^48) 7975075841 10 Manual.Count131072.C060815.packed 64 cuts60815 = true := by
 decide +kernel
def cuts60816 : List PrefixCut := [⟨42,131397892,131397971⟩,
⟨64,200890321,200890441⟩]
theorem checked60816 : checkPrefixCuts (2^48) 7975206913 10 Manual.Count131072.C060816.packed 64 cuts60816 = true := by
 decide +kernel
def pointBounds60816 : List (Nat × Nat × Nat) := [(7975292928,114083656575240,114084045077828)]
theorem point_links_checked60816 : (cuts60816.take 1).map (fun c => (7975206913-1+2*2^10*c.k,114083525177348+c.lower,114083913679857+c.upper)) = pointBounds60816 := by
 decide +kernel
def cuts60817 : List PrefixCut := [⟨64,204169268,204169384⟩]
theorem checked60817 : checkPrefixCuts (2^48) 7975337985 10 Manual.Count131072.C060817.packed 64 cuts60817 = true := by
 decide +kernel
def cuts60818 : List PrefixCut := [⟨36,114488604,114488671⟩,
⟨64,201942498,201942616⟩]
theorem checked60818 : checkPrefixCuts (2^48) 7975469057 10 Manual.Count131072.C060818.packed 64 cuts60818 = true := by
 decide +kernel
def pointBounds60818 : List (Nat × Nat × Nat) := [(7975542784,114084044725541,114084433228353)]
theorem point_links_checked60818 : (cuts60818.take 1).map (fun c => (7975469057-1+2*2^10*c.k,114083930236937+c.lower,114084318739682+c.upper)) = pointBounds60818 := by
 decide +kernel
def cuts60819 : List PrefixCut := [⟨64,202892047,202892162⟩]
theorem checked60819 : checkPrefixCuts (2^48) 7975600129 10 Manual.Count131072.C060819.packed 64 cuts60819 = true := by
 decide +kernel
def cuts60820 : List PrefixCut := [⟨30,94192447,94192498⟩,
⟨64,203559248,203559359⟩]
theorem checked60820 : checkPrefixCuts (2^48) 7975731201 10 Manual.Count131072.C060820.packed 64 cuts60820 = true := by
 decide +kernel
def pointBounds60820 : List (Nat × Nat × Nat) := [(7975792640,114084429263929,114084817766958)]
theorem point_links_checked60820 : (cuts60820.take 1).map (fun c => (7975731201-1+2*2^10*c.k,114084335071482+c.lower,114084723574460+c.upper)) = pointBounds60820 := by
 decide +kernel
def cuts60821 : List PrefixCut := [⟨64,203979385,203979507⟩]
theorem checked60821 : checkPrefixCuts (2^48) 7975862273 10 Manual.Count131072.C060821.packed 64 cuts60821 = true := by
 decide +kernel
def cuts60822 : List PrefixCut := [⟨24,76614928,76614971⟩,
⟨64,203481990,203482109⟩]
theorem checked60822 : checkPrefixCuts (2^48) 7975993345 10 Manual.Count131072.C060822.packed 64 cuts60822 = true := by
 decide +kernel
def pointBounds60822 : List (Nat × Nat × Nat) := [(7976042496,114084819225043,114085207728297)]
theorem point_links_checked60822 : (cuts60822.take 1).map (fun c => (7975993345-1+2*2^10*c.k,114084742610115+c.lower,114085131113326+c.upper)) = pointBounds60822 := by
 decide +kernel
def cuts60823 : List PrefixCut := [⟨64,207254602,207254719⟩]
theorem checked60823 : checkPrefixCuts (2^48) 7976124417 10 Manual.Count131072.C060823.packed 64 cuts60823 = true := by
 decide +kernel
def cuts60824 : List PrefixCut := [⟨18,58579777,58579812⟩,
⟨64,203581167,203581286⟩]
theorem checked60824 : checkPrefixCuts (2^48) 7976255489 10 Manual.Count131072.C060824.packed 64 cuts60824 = true := by
 decide +kernel
def pointBounds60824 : List (Nat × Nat × Nat) := [(7976292352,114085211926484,114085600429966)]
theorem point_links_checked60824 : (cuts60824.take 1).map (fun c => (7976255489-1+2*2^10*c.k,114085153346707+c.lower,114085541850154+c.upper)) = pointBounds60824 := by
 decide +kernel
def cuts60825 : List PrefixCut := [⟨64,203013187,203013306⟩]
theorem checked60825 : checkPrefixCuts (2^48) 7976386561 10 Manual.Count131072.C060825.packed 64 cuts60825 = true := by
 decide +kernel
def cuts60826 : List PrefixCut := [⟨12,37087569,37087592⟩,
⟨64,201316057,201316173⟩]
theorem checked60826 : checkPrefixCuts (2^48) 7976517633 10 Manual.Count131072.C060826.packed 64 cuts60826 = true := by
 decide +kernel
def pointBounds60826 : List (Nat × Nat × Nat) := [(7976542208,114085597028630,114085985532338)]
theorem point_links_checked60826 : (cuts60826.take 1).map (fun c => (7976517633-1+2*2^10*c.k,114085559941061+c.lower,114085948444746+c.upper)) = pointBounds60826 := by
 decide +kernel
def cuts60827 : List PrefixCut := [⟨64,202300778,202300893⟩]
theorem checked60827 : checkPrefixCuts (2^48) 7976648705 10 Manual.Count131072.C060827.packed 64 cuts60827 = true := by
 decide +kernel
def cuts60828 : List PrefixCut := [⟨6,19407716,19407728⟩,
⟨64,204132366,204132485⟩]
theorem checked60828 : checkPrefixCuts (2^48) 7976779777 10 Manual.Count131072.C060828.packed 64 cuts60828 = true := by
 decide +kernel
def pointBounds60828 : List (Nat × Nat × Nat) := [(7976792064,114085982965612,114086371469540)]
theorem point_links_checked60828 : (cuts60828.take 1).map (fun c => (7976779777-1+2*2^10*c.k,114085963557896+c.lower,114086352061812+c.upper)) = pointBounds60828 := by
 decide +kernel
def cuts60829 : List PrefixCut := [⟨64,205222879,205222992⟩]
theorem checked60829 : checkPrefixCuts (2^48) 7976910849 10 Manual.Count131072.C060829.packed 64 cuts60829 = true := by
 decide +kernel
def pointBounds60829 : List (Nat × Nat × Nat) := [(7977041920,114086372913141,114086761417289)]
theorem point_links_checked60829 : (cuts60829.take 1).map (fun c => (7976910849-1+2*2^10*c.k,114086167690262+c.lower,114086556194297+c.upper)) = pointBounds60829 := by
 decide +kernel
def cuts60830 : List PrefixCut := [⟨64,201973248,201973363⟩]
theorem checked60830 : checkPrefixCuts (2^48) 7977041921 10 Manual.Count131072.C060830.packed 64 cuts60830 = true := by
 decide +kernel
def cuts60831 : List PrefixCut := [⟨58,185350957,185351067⟩,
⟨64,204581004,204581125⟩]
theorem checked60831 : checkPrefixCuts (2^48) 7977172993 10 Manual.Count131072.C060831.packed 64 cuts60831 = true := by
 decide +kernel
def pointBounds60831 : List (Nat × Nat × Nat) := [(7977291776,114086760237346,114087148741719)]
theorem point_links_checked60831 : (cuts60831.take 1).map (fun c => (7977172993-1+2*2^10*c.k,114086574886389+c.lower,114086963390652+c.upper)) = pointBounds60831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000025
