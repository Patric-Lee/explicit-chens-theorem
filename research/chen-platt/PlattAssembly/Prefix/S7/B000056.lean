import PlattAssemblyKernel
import PlattCertificates.Count131072.C061792
import PlattCertificates.Count131072.C061793
import PlattCertificates.Count131072.C061794
import PlattCertificates.Count131072.C061795
import PlattCertificates.Count131072.C061796
import PlattCertificates.Count131072.C061797
import PlattCertificates.Count131072.C061798
import PlattCertificates.Count131072.C061799
import PlattCertificates.Count131072.C061800
import PlattCertificates.Count131072.C061801
import PlattCertificates.Count131072.C061802
import PlattCertificates.Count131072.C061803
import PlattCertificates.Count131072.C061804
import PlattCertificates.Count131072.C061805
import PlattCertificates.Count131072.C061806
import PlattCertificates.Count131072.C061807
import PlattCertificates.Count131072.C061808
import PlattCertificates.Count131072.C061809
import PlattCertificates.Count131072.C061810
import PlattCertificates.Count131072.C061811
import PlattCertificates.Count131072.C061812
import PlattCertificates.Count131072.C061813
import PlattCertificates.Count131072.C061814
import PlattCertificates.Count131072.C061815
import PlattCertificates.Count131072.C061816
import PlattCertificates.Count131072.C061817
import PlattCertificates.Count131072.C061818
import PlattCertificates.Count131072.C061819
import PlattCertificates.Count131072.C061820
import PlattCertificates.Count131072.C061821
import PlattCertificates.Count131072.C061822
import PlattCertificates.Count131072.C061823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61792 : List PrefixCut := [⟨24,74405466,74405508⟩,
⟨64,200289322,200289436⟩]
theorem checked61792 : checkPrefixCuts (2^48) 8103133185 10 Manual.Count131072.C061792.packed 64 cuts61792 = true := by
 decide +kernel
def pointBounds61792 : List (Nat × Nat × Nat) := [(8103182336,114280046124475,114280434739555)]
theorem point_links_checked61792 : (cuts61792.take 1).map (fun c => (8103133185-1+2*2^10*c.k,114279971719009+c.lower,114280360334047+c.upper)) = pointBounds61792 := by
 decide +kernel
def cuts61793 : List PrefixCut := [⟨64,199139807,199139923⟩]
theorem checked61793 : checkPrefixCuts (2^48) 8103264257 10 Manual.Count131072.C061793.packed 64 cuts61793 = true := by
 decide +kernel
def cuts61794 : List PrefixCut := [⟨20,60647900,60647938⟩,
⟨64,199032381,199032496⟩]
theorem checked61794 : checkPrefixCuts (2^48) 8103395329 10 Manual.Count131072.C061794.packed 64 cuts61794 = true := by
 decide +kernel
def pointBounds61794 : List (Nat × Nat × Nat) := [(8103436288,114280431796038,114280820411344)]
theorem point_links_checked61794 : (cuts61794.take 1).map (fun c => (8103395329-1+2*2^10*c.k,114280371148138+c.lower,114280759763406+c.upper)) = pointBounds61794 := by
 decide +kernel
def cuts61795 : List PrefixCut := [⟨64,201147976,201148090⟩]
theorem checked61795 : checkPrefixCuts (2^48) 8103526401 10 Manual.Count131072.C061795.packed 64 cuts61795 = true := by
 decide +kernel
def cuts61796 : List PrefixCut := [⟨16,50329903,50329932⟩,
⟨64,200623699,200623817⟩]
theorem checked61796 : checkPrefixCuts (2^48) 8103657473 10 Manual.Count131072.C061796.packed 64 cuts61796 = true := by
 decide +kernel
def pointBounds61796 : List (Nat × Nat × Nat) := [(8103690240,114280821658398,114281210273924)]
theorem point_links_checked61796 : (cuts61796.take 1).map (fun c => (8103657473-1+2*2^10*c.k,114280771328495+c.lower,114281159943992+c.upper)) = pointBounds61796 := by
 decide +kernel
def cuts61797 : List PrefixCut := [⟨64,198223860,198223979⟩]
theorem checked61797 : checkPrefixCuts (2^48) 8103788545 10 Manual.Count131072.C061797.packed 64 cuts61797 = true := by
 decide +kernel
def cuts61798 : List PrefixCut := [⟨12,37442310,37442333⟩,
⟨64,195372565,195372678⟩]
theorem checked61798 : checkPrefixCuts (2^48) 8103919617 10 Manual.Count131072.C061798.packed 64 cuts61798 = true := by
 decide +kernel
def pointBounds61798 : List (Nat × Nat × Nat) := [(8103944192,114281207618364,114281596234121)]
theorem point_links_checked61798 : (cuts61798.take 1).map (fun c => (8103919617-1+2*2^10*c.k,114281170176054+c.lower,114281558791788+c.upper)) = pointBounds61798 := by
 decide +kernel
def cuts61799 : List PrefixCut := [⟨64,201169694,201169808⟩]
theorem checked61799 : checkPrefixCuts (2^48) 8104050689 10 Manual.Count131072.C061799.packed 64 cuts61799 = true := by
 decide +kernel
def cuts61800 : List PrefixCut := [⟨8,25041788,25041802⟩,
⟨64,197102823,197102936⟩]
theorem checked61800 : checkPrefixCuts (2^48) 8104181761 10 Manual.Count131072.C061800.packed 64 cuts61800 = true := by
 decide +kernel
def pointBounds61800 : List (Nat × Nat × Nat) := [(8104198144,114281591760101,114281980376076)]
theorem point_links_checked61800 : (cuts61800.take 1).map (fun c => (8104181761-1+2*2^10*c.k,114281566718313+c.lower,114281955334274+c.upper)) = pointBounds61800 := by
 decide +kernel
def cuts61801 : List PrefixCut := [⟨64,198419420,198419532⟩]
theorem checked61801 : checkPrefixCuts (2^48) 8104312833 10 Manual.Count131072.C061801.packed 64 cuts61801 = true := by
 decide +kernel
def cuts61802 : List PrefixCut := [⟨4,12572591,12572599⟩,
⟨64,201090477,201090591⟩]
theorem checked61802 : checkPrefixCuts (2^48) 8104443905 10 Manual.Count131072.C061802.packed 64 cuts61802 = true := by
 decide +kernel
def pointBounds61802 : List (Nat × Nat × Nat) := [(8104452096,114281974813147,114282363429341)]
theorem point_links_checked61802 : (cuts61802.take 1).map (fun c => (8104443905-1+2*2^10*c.k,114281962240556+c.lower,114282350856742+c.upper)) = pointBounds61802 := by
 decide +kernel
def cuts61803 : List PrefixCut := [⟨64,199836936,199837050⟩]
theorem checked61803 : checkPrefixCuts (2^48) 8104574977 10 Manual.Count131072.C061803.packed 64 cuts61803 = true := by
 decide +kernel
def pointBounds61803 : List (Nat × Nat × Nat) := [(8104706048,114282363167969,114282751784383)]
theorem point_links_checked61803 : (cuts61803.take 1).map (fun c => (8104574977-1+2*2^10*c.k,114282163331033+c.lower,114282551947333+c.upper)) = pointBounds61803 := by
 decide +kernel
def cuts61804 : List PrefixCut := [⟨64,197367912,197368025⟩]
theorem checked61804 : checkPrefixCuts (2^48) 8104706049 10 Manual.Count131072.C061804.packed 64 cuts61804 = true := by
 decide +kernel
def cuts61805 : List PrefixCut := [⟨60,182327160,182327266⟩,
⟨64,195107323,195107437⟩]
theorem checked61805 : checkPrefixCuts (2^48) 8104837121 10 Manual.Count131072.C061805.packed 64 cuts61805 = true := by
 decide +kernel
def pointBounds61805 : List (Nat × Nat × Nat) := [(8104960000,114282742863041,114283131479674)]
theorem point_links_checked61805 : (cuts61805.take 1).map (fun c => (8104837121-1+2*2^10*c.k,114282560535881+c.lower,114282949152408+c.upper)) = pointBounds61805 := by
 decide +kernel
def cuts61806 : List PrefixCut := [⟨64,200313430,200313550⟩]
theorem checked61806 : checkPrefixCuts (2^48) 8104968193 10 Manual.Count131072.C061806.packed 64 cuts61806 = true := by
 decide +kernel
def cuts61807 : List PrefixCut := [⟨56,174681220,174681319⟩,
⟨64,199129450,199129563⟩]
theorem checked61807 : checkPrefixCuts (2^48) 8105099265 10 Manual.Count131072.C061807.packed 64 cuts61807 = true := by
 decide +kernel
def pointBounds61807 : List (Nat × Nat × Nat) := [(8105213952,114283130637854,114283519254714)]
theorem point_links_checked61807 : (cuts61807.take 1).map (fun c => (8105099265-1+2*2^10*c.k,114282955956634+c.lower,114283344573395+c.upper)) = pointBounds61807 := by
 decide +kernel
def cuts61808 : List PrefixCut := [⟨64,198327510,198327627⟩]
theorem checked61808 : checkPrefixCuts (2^48) 8105230337 10 Manual.Count131072.C061808.packed 64 cuts61808 = true := by
 decide +kernel
def cuts61809 : List PrefixCut := [⟨52,163979830,163979924⟩,
⟨64,201970614,201970729⟩]
theorem checked61809 : checkPrefixCuts (2^48) 8105361409 10 Manual.Count131072.C061809.packed 64 cuts61809 = true := by
 decide +kernel
def pointBounds61809 : List (Nat × Nat × Nat) := [(8105467904,114283517393424,114283906010509)]
theorem point_links_checked61809 : (cuts61809.take 1).map (fun c => (8105361409-1+2*2^10*c.k,114283353413594+c.lower,114283742030585+c.upper)) = pointBounds61809 := by
 decide +kernel
def cuts61810 : List PrefixCut := [⟨64,198043288,198043401⟩]
theorem checked61810 : checkPrefixCuts (2^48) 8105492481 10 Manual.Count131072.C061810.packed 64 cuts61810 = true := by
 decide +kernel
def cuts61811 : List PrefixCut := [⟨48,148070246,148070332⟩,
⟨64,198699859,198699974⟩]
theorem checked61811 : checkPrefixCuts (2^48) 8105623553 10 Manual.Count131072.C061811.packed 64 cuts61811 = true := by
 decide +kernel
def pointBounds61811 : List (Nat × Nat × Nat) := [(8105721856,114283901497742,114284290115047)]
theorem point_links_checked61811 : (cuts61811.take 1).map (fun c => (8105623553-1+2*2^10*c.k,114283753427496+c.lower,114284142044715+c.upper)) = pointBounds61811 := by
 decide +kernel
def cuts61812 : List PrefixCut := [⟨64,201335771,201335885⟩]
theorem checked61812 : checkPrefixCuts (2^48) 8105754625 10 Manual.Count131072.C061812.packed 64 cuts61812 = true := by
 decide +kernel
def cuts61813 : List PrefixCut := [⟨44,136641145,136641221⟩,
⟨64,199630993,199631103⟩]
theorem checked61813 : checkPrefixCuts (2^48) 8105885697 10 Manual.Count131072.C061813.packed 64 cuts61813 = true := by
 decide +kernel
def pointBounds61813 : List (Nat × Nat × Nat) := [(8105975808,114284290104271,114284678721795)]
theorem point_links_checked61813 : (cuts61813.take 1).map (fun c => (8105885697-1+2*2^10*c.k,114284153463126+c.lower,114284542080574+c.upper)) = pointBounds61813 := by
 decide +kernel
def cuts61814 : List PrefixCut := [⟨64,199558338,199558452⟩]
theorem checked61814 : checkPrefixCuts (2^48) 8106016769 10 Manual.Count131072.C061814.packed 64 cuts61814 = true := by
 decide +kernel
def cuts61815 : List PrefixCut := [⟨40,122921031,122921103⟩,
⟨64,198548111,198548225⟩]
theorem checked61815 : checkPrefixCuts (2^48) 8106147841 10 Manual.Count131072.C061815.packed 64 cuts61815 = true := by
 decide +kernel
def pointBounds61815 : List (Nat × Nat × Nat) := [(8106229760,114284675573488,114285064191232)]
theorem point_links_checked61815 : (cuts61815.take 1).map (fun c => (8106147841-1+2*2^10*c.k,114284552652457+c.lower,114284941270129+c.upper)) = pointBounds61815 := by
 decide +kernel
def cuts61816 : List PrefixCut := [⟨64,200281040,200281155⟩]
theorem checked61816 : checkPrefixCuts (2^48) 8106278913 10 Manual.Count131072.C061816.packed 64 cuts61816 = true := by
 decide +kernel
def cuts61817 : List PrefixCut := [⟨36,112292084,112292148⟩,
⟨64,200833365,200833481⟩]
theorem checked61817 : checkPrefixCuts (2^48) 8106409985 10 Manual.Count131072.C061817.packed 64 cuts61817 = true := by
 decide +kernel
def pointBounds61817 : List (Nat × Nat × Nat) := [(8106483712,114285063773692,114285452391657)]
theorem point_links_checked61817 : (cuts61817.take 1).map (fun c => (8106409985-1+2*2^10*c.k,114284951481608+c.lower,114285340099509+c.upper)) = pointBounds61817 := by
 decide +kernel
def cuts61818 : List PrefixCut := [⟨64,201593986,201594097⟩]
theorem checked61818 : checkPrefixCuts (2^48) 8106541057 10 Manual.Count131072.C061818.packed 64 cuts61818 = true := by
 decide +kernel
def cuts61819 : List PrefixCut := [⟨32,100413844,100413900⟩,
⟨64,198431134,198431243⟩]
theorem checked61819 : checkPrefixCuts (2^48) 8106672129 10 Manual.Count131072.C061819.packed 64 cuts61819 = true := by
 decide +kernel
def pointBounds61819 : List (Nat × Nat × Nat) := [(8106737664,114285454322803,114285842940987)]
theorem point_links_checked61819 : (cuts61819.take 1).map (fun c => (8106672129-1+2*2^10*c.k,114285353908959+c.lower,114285742527087+c.upper)) = pointBounds61819 := by
 decide +kernel
def cuts61820 : List PrefixCut := [⟨64,200580585,200580697⟩]
theorem checked61820 : checkPrefixCuts (2^48) 8106803201 10 Manual.Count131072.C061820.packed 64 cuts61820 = true := by
 decide +kernel
def cuts61821 : List PrefixCut := [⟨28,86418427,86418478⟩,
⟨64,197556701,197556817⟩]
theorem checked61821 : checkPrefixCuts (2^48) 8106934273 10 Manual.Count131072.C061821.packed 64 cuts61821 = true := by
 decide +kernel
def pointBounds61821 : List (Nat × Nat × Nat) := [(8106991616,114285839339105,114286227957505)]
theorem point_links_checked61821 : (cuts61821.take 1).map (fun c => (8106934273-1+2*2^10*c.k,114285752920678+c.lower,114286141539027+c.upper)) = pointBounds61821 := by
 decide +kernel
def cuts61822 : List PrefixCut := [⟨64,202657255,202657372⟩]
theorem checked61822 : checkPrefixCuts (2^48) 8107065345 10 Manual.Count131072.C061822.packed 64 cuts61822 = true := by
 decide +kernel
def cuts61823 : List PrefixCut := [⟨24,74576488,74576530⟩,
⟨64,198175267,198175378⟩]
theorem checked61823 : checkPrefixCuts (2^48) 8107196417 10 Manual.Count131072.C061823.packed 64 cuts61823 = true := by
 decide +kernel
def pointBounds61823 : List (Nat × Nat × Nat) := [(8107245568,114286227711122,114286616329746)]
theorem point_links_checked61823 : (cuts61823.take 1).map (fun c => (8107196417-1+2*2^10*c.k,114286153134634+c.lower,114286541753216+c.upper)) = pointBounds61823 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000056
