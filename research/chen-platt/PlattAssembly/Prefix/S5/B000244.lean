import PlattAssemblyKernel
import PlattCertificates.Count131072.C047808
import PlattCertificates.Count131072.C047809
import PlattCertificates.Count131072.C047810
import PlattCertificates.Count131072.C047811
import PlattCertificates.Count131072.C047812
import PlattCertificates.Count131072.C047813
import PlattCertificates.Count131072.C047814
import PlattCertificates.Count131072.C047815
import PlattCertificates.Count131072.C047816
import PlattCertificates.Count131072.C047817
import PlattCertificates.Count131072.C047818
import PlattCertificates.Count131072.C047819
import PlattCertificates.Count131072.C047820
import PlattCertificates.Count131072.C047821
import PlattCertificates.Count131072.C047822
import PlattCertificates.Count131072.C047823
import PlattCertificates.Count131072.C047824
import PlattCertificates.Count131072.C047825
import PlattCertificates.Count131072.C047826
import PlattCertificates.Count131072.C047827
import PlattCertificates.Count131072.C047828
import PlattCertificates.Count131072.C047829
import PlattCertificates.Count131072.C047830
import PlattCertificates.Count131072.C047831
import PlattCertificates.Count131072.C047832
import PlattCertificates.Count131072.C047833
import PlattCertificates.Count131072.C047834
import PlattCertificates.Count131072.C047835
import PlattCertificates.Count131072.C047836
import PlattCertificates.Count131072.C047837
import PlattCertificates.Count131072.C047838
import PlattCertificates.Count131072.C047839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47808 : List PrefixCut := [⟨64,261620497,261620637⟩]
theorem checked47808 : checkPrefixCuts (2^48) 6270222337 10 Manual.Count131072.C047808.packed 64 cuts47808 = true := by
 decide +kernel
def cuts47809 : List PrefixCut := [⟨16,65090034,65090070⟩,
⟨64,260672337,260672491⟩]
theorem checked47809 : checkPrefixCuts (2^48) 6270353409 10 Manual.Count131072.C047809.packed 64 cuts47809 = true := by
 decide +kernel
def pointBounds47809 : List (Nat × Nat × Nat) := [(6270386176,111098732281285,111099119084721)]
theorem point_links_checked47809 : (cuts47809.take 1).map (fun c => (6270353409-1+2*2^10*c.k,111098667191251+c.lower,111099053994651+c.upper)) = pointBounds47809 := by
 decide +kernel
def cuts47810 : List PrefixCut := [⟨48,194187708,194187822⟩,
⟨64,260666894,260667046⟩]
theorem checked47810 : checkPrefixCuts (2^48) 6270484481 10 Manual.Count131072.C047810.packed 64 cuts47810 = true := by
 decide +kernel
def pointBounds47810 : List (Nat × Nat × Nat) := [(6270582784,111099122051296,111099508854964)]
theorem point_links_checked47810 : (cuts47810.take 1).map (fun c => (6270484481-1+2*2^10*c.k,111098927863588+c.lower,111099314667142+c.upper)) = pointBounds47810 := by
 decide +kernel
def cuts47811 : List PrefixCut := [⟨64,260885895,260886038⟩]
theorem checked47811 : checkPrefixCuts (2^48) 6270615553 10 Manual.Count131072.C047811.packed 64 cuts47811 = true := by
 decide +kernel
def cuts47812 : List PrefixCut := [⟨16,63200708,63200742⟩,
⟨64,257783226,257783374⟩]
theorem checked47812 : checkPrefixCuts (2^48) 6270746625 10 Manual.Count131072.C047812.packed 64 cuts47812 = true := by
 decide +kernel
def pointBounds47812 : List (Nat × Nat × Nat) := [(6270779392,111099512617085,111099899420968)]
theorem point_links_checked47812 : (cuts47812.take 1).map (fun c => (6270746625-1+2*2^10*c.k,111099449416377+c.lower,111099836220226+c.upper)) = pointBounds47812 := by
 decide +kernel
def cuts47813 : List PrefixCut := [⟨48,195791398,195791515⟩,
⟨64,261144283,261144440⟩]
theorem checked47813 : checkPrefixCuts (2^48) 6270877697 10 Manual.Count131072.C047813.packed 64 cuts47813 = true := by
 decide +kernel
def pointBounds47813 : List (Nat × Nat × Nat) := [(6270976000,111099902991001,111100289795115)]
theorem point_links_checked47813 : (cuts47813.take 1).map (fun c => (6270877697-1+2*2^10*c.k,111099707199603+c.lower,111100094003600+c.upper)) = pointBounds47813 := by
 decide +kernel
def cuts47814 : List PrefixCut := [⟨64,263338206,263338355⟩]
theorem checked47814 : checkPrefixCuts (2^48) 6271008769 10 Manual.Count131072.C047814.packed 64 cuts47814 = true := by
 decide +kernel
def cuts47815 : List PrefixCut := [⟨16,65710252,65710287⟩,
⟨64,260325464,260325616⟩]
theorem checked47815 : checkPrefixCuts (2^48) 6271139841 10 Manual.Count131072.C047815.packed 64 cuts47815 = true := by
 decide +kernel
def pointBounds47815 : List (Nat × Nat × Nat) := [(6271172608,111100297392344,111100684196682)]
theorem point_links_checked47815 : (cuts47815.take 1).map (fun c => (6271139841-1+2*2^10*c.k,111100231682092+c.lower,111100618486395+c.upper)) = pointBounds47815 := by
 decide +kernel
def cuts47816 : List PrefixCut := [⟨48,199459524,199459636⟩,
⟨64,264583896,264584046⟩]
theorem checked47816 : checkPrefixCuts (2^48) 6271270913 10 Manual.Count131072.C047816.packed 64 cuts47816 = true := by
 decide +kernel
def pointBounds47816 : List (Nat × Nat × Nat) := [(6271369216,111100691467080,111101078271647)]
theorem point_links_checked47816 : (cuts47816.take 1).map (fun c => (6271270913-1+2*2^10*c.k,111100492007556+c.lower,111100878812011+c.upper)) = pointBounds47816 := by
 decide +kernel
def cuts47817 : List PrefixCut := [⟨64,257801167,257801317⟩]
theorem checked47817 : checkPrefixCuts (2^48) 6271401985 10 Manual.Count131072.C047817.packed 64 cuts47817 = true := by
 decide +kernel
def cuts47818 : List PrefixCut := [⟨16,67366737,67366777⟩,
⟨64,258872983,258873139⟩]
theorem checked47818 : checkPrefixCuts (2^48) 6271533057 10 Manual.Count131072.C047818.packed 64 cuts47818 = true := by
 decide +kernel
def pointBounds47818 : List (Nat × Nat × Nat) := [(6271565824,111101081759356,111101468564151)]
theorem point_links_checked47818 : (cuts47818.take 1).map (fun c => (6271533057-1+2*2^10*c.k,111101014392619+c.lower,111101401197374+c.upper)) = pointBounds47818 := by
 decide +kernel
def cuts47819 : List PrefixCut := [⟨48,199626532,199626646⟩,
⟨64,264567307,264567456⟩]
theorem checked47819 : checkPrefixCuts (2^48) 6271664129 10 Manual.Count131072.C047819.packed 64 cuts47819 = true := by
 decide +kernel
def pointBounds47819 : List (Nat × Nat × Nat) := [(6271762432,111101472892134,111101859697159)]
theorem point_links_checked47819 : (cuts47819.take 1).map (fun c => (6271664129-1+2*2^10*c.k,111101273265602+c.lower,111101660070513+c.upper)) = pointBounds47819 := by
 decide +kernel
def cuts47820 : List PrefixCut := [⟨64,259310916,259311065⟩]
theorem checked47820 : checkPrefixCuts (2^48) 6271795201 10 Manual.Count131072.C047820.packed 64 cuts47820 = true := by
 decide +kernel
def cuts47821 : List PrefixCut := [⟨16,64804442,64804479⟩,
⟨64,261594249,261594393⟩]
theorem checked47821 : checkPrefixCuts (2^48) 6271926273 10 Manual.Count131072.C047821.packed 64 cuts47821 = true := by
 decide +kernel
def pointBounds47821 : List (Nat × Nat × Nat) := [(6271959040,111101861948267,111102248753513)]
theorem point_links_checked47821 : (cuts47821.take 1).map (fun c => (6271926273-1+2*2^10*c.k,111101797143825+c.lower,111102183949034+c.upper)) = pointBounds47821 := by
 decide +kernel
def cuts47822 : List PrefixCut := [⟨48,196382842,196382956⟩,
⟨64,259703979,259704129⟩]
theorem checked47822 : checkPrefixCuts (2^48) 6272057345 10 Manual.Count131072.C047822.packed 64 cuts47822 = true := by
 decide +kernel
def pointBounds47822 : List (Nat × Nat × Nat) := [(6272155648,111102255120916,111102641926383)]
theorem point_links_checked47822 : (cuts47822.take 1).map (fun c => (6272057345-1+2*2^10*c.k,111102058738074+c.lower,111102445543427+c.upper)) = pointBounds47822 := by
 decide +kernel
def cuts47823 : List PrefixCut := [⟨64,262615497,262615646⟩]
theorem checked47823 : checkPrefixCuts (2^48) 6272188417 10 Manual.Count131072.C047823.packed 64 cuts47823 = true := by
 decide +kernel
def cuts47824 : List PrefixCut := [⟨16,65159384,65159424⟩,
⟨64,261084243,261084391⟩]
theorem checked47824 : checkPrefixCuts (2^48) 6272319489 10 Manual.Count131072.C047824.packed 64 cuts47824 = true := by
 decide +kernel
def pointBounds47824 : List (Nat × Nat × Nat) := [(6272352256,111102646216934,111103033022626)]
theorem point_links_checked47824 : (cuts47824.take 1).map (fun c => (6272319489-1+2*2^10*c.k,111102581057550+c.lower,111102967863202+c.upper)) = pointBounds47824 := by
 decide +kernel
def cuts47825 : List PrefixCut := [⟨48,195338428,195338539⟩,
⟨64,263412239,263412385⟩]
theorem checked47825 : checkPrefixCuts (2^48) 6272450561 10 Manual.Count131072.C047825.packed 64 cuts47825 = true := by
 decide +kernel
def pointBounds47825 : List (Nat × Nat × Nat) := [(6272548864,111103037480221,111103424286132)]
theorem point_links_checked47825 : (cuts47825.take 1).map (fun c => (6272450561-1+2*2^10*c.k,111102842141793+c.lower,111103228947593+c.upper)) = pointBounds47825 := by
 decide +kernel
def cuts47826 : List PrefixCut := [⟨64,258201428,258201578⟩]
theorem checked47826 : checkPrefixCuts (2^48) 6272581633 10 Manual.Count131072.C047826.packed 64 cuts47826 = true := by
 decide +kernel
def cuts47827 : List PrefixCut := [⟨16,67488687,67488727⟩,
⟨64,260933289,260933440⟩]
theorem checked47827 : checkPrefixCuts (2^48) 6272712705 10 Manual.Count131072.C047827.packed 64 cuts47827 = true := by
 decide +kernel
def pointBounds47827 : List (Nat × Nat × Nat) := [(6272745472,111103431244147,111103818050283)]
theorem point_links_checked47827 : (cuts47827.take 1).map (fun c => (6272712705-1+2*2^10*c.k,111103363755460+c.lower,111103750561556+c.upper)) = pointBounds47827 := by
 decide +kernel
def cuts47828 : List PrefixCut := [⟨48,195909504,195909613⟩,
⟨64,258953475,258953622⟩]
theorem checked47828 : checkPrefixCuts (2^48) 6272843777 10 Manual.Count131072.C047828.packed 64 cuts47828 = true := by
 decide +kernel
def pointBounds47828 : List (Nat × Nat × Nat) := [(6272942080,111103820598253,111104207404609)]
theorem point_links_checked47828 : (cuts47828.take 1).map (fun c => (6272843777-1+2*2^10*c.k,111103624688749+c.lower,111104011494996+c.upper)) = pointBounds47828 := by
 decide +kernel
def cuts47829 : List PrefixCut := [⟨64,262492842,262492989⟩]
theorem checked47829 : checkPrefixCuts (2^48) 6272974849 10 Manual.Count131072.C047829.packed 64 cuts47829 = true := by
 decide +kernel
def cuts47830 : List PrefixCut := [⟨16,64298689,64298724⟩,
⟨64,261904027,261904176⟩]
theorem checked47830 : checkPrefixCuts (2^48) 6273105921 10 Manual.Count131072.C047830.packed 64 cuts47830 = true := by
 decide +kernel
def pointBounds47830 : List (Nat × Nat × Nat) := [(6273138688,111104210433755,111104597240331)]
theorem point_links_checked47830 : (cuts47830.take 1).map (fun c => (6273105921-1+2*2^10*c.k,111104146135066+c.lower,111104532941607+c.upper)) = pointBounds47830 := by
 decide +kernel
def cuts47831 : List PrefixCut := [⟨48,198634234,198634347⟩,
⟨64,265218853,265219006⟩]
theorem checked47831 : checkPrefixCuts (2^48) 6273236993 10 Manual.Count131072.C047831.packed 64 cuts47831 = true := by
 decide +kernel
def pointBounds47831 : List (Nat × Nat × Nat) := [(6273335296,111104606673327,111104993480130)]
theorem point_links_checked47831 : (cuts47831.take 1).map (fun c => (6273236993-1+2*2^10*c.k,111104408039093+c.lower,111104794845783+c.upper)) = pointBounds47831 := by
 decide +kernel
def cuts47832 : List PrefixCut := [⟨64,258752355,258752504⟩]
theorem checked47832 : checkPrefixCuts (2^48) 6273368065 10 Manual.Count131072.C047832.packed 64 cuts47832 = true := by
 decide +kernel
def cuts47833 : List PrefixCut := [⟨16,67794297,67794337⟩,
⟨64,260048132,260048277⟩]
theorem checked47833 : checkPrefixCuts (2^48) 6273499137 10 Manual.Count131072.C047833.packed 64 cuts47833 = true := by
 decide +kernel
def pointBounds47833 : List (Nat × Nat × Nat) := [(6273531904,111104999804598,111105386611630)]
theorem point_links_checked47833 : (cuts47833.take 1).map (fun c => (6273499137-1+2*2^10*c.k,111104932010301+c.lower,111105318817293+c.upper)) = pointBounds47833 := by
 decide +kernel
def cuts47834 : List PrefixCut := [⟨48,191847015,191847125⟩,
⟨64,256857171,256857315⟩]
theorem checked47834 : checkPrefixCuts (2^48) 6273630209 10 Manual.Count131072.C047834.packed 64 cuts47834 = true := by
 decide +kernel
def pointBounds47834 : List (Nat × Nat × Nat) := [(6273728512,111105383905448,111105770712695)]
theorem point_links_checked47834 : (cuts47834.take 1).map (fun c => (6273630209-1+2*2^10*c.k,111105192058433+c.lower,111105578865570+c.upper)) = pointBounds47834 := by
 decide +kernel
def cuts47835 : List PrefixCut := [⟨64,266946417,266946568⟩]
theorem checked47835 : checkPrefixCuts (2^48) 6273761281 10 Manual.Count131072.C047835.packed 64 cuts47835 = true := by
 decide +kernel
def cuts47836 : List PrefixCut := [⟨16,64649540,64649582⟩,
⟨64,259358830,259358982⟩]
theorem checked47836 : checkPrefixCuts (2^48) 6273892353 10 Manual.Count131072.C047836.packed 64 cuts47836 = true := by
 decide +kernel
def pointBounds47836 : List (Nat × Nat × Nat) := [(6273925120,111105780511561,111106167319035)]
theorem point_links_checked47836 : (cuts47836.take 1).map (fun c => (6273892353-1+2*2^10*c.k,111105715862021+c.lower,111106102669453+c.upper)) = pointBounds47836 := by
 decide +kernel
def cuts47837 : List PrefixCut := [⟨48,198295268,198295386⟩,
⟨64,262897583,262897737⟩]
theorem checked47837 : checkPrefixCuts (2^48) 6274023425 10 Manual.Count131072.C047837.packed 64 cuts47837 = true := by
 decide +kernel
def pointBounds47837 : List (Nat × Nat × Nat) := [(6274121728,111106173516119,111106560323821)]
theorem point_links_checked47837 : (cuts47837.take 1).map (fun c => (6274023425-1+2*2^10*c.k,111105975220851+c.lower,111106362028435+c.upper)) = pointBounds47837 := by
 decide +kernel
def cuts47838 : List PrefixCut := [⟨64,257912419,257912567⟩]
theorem checked47838 : checkPrefixCuts (2^48) 6274154497 10 Manual.Count131072.C047838.packed 64 cuts47838 = true := by
 decide +kernel
def cuts47839 : List PrefixCut := [⟨16,66484817,66484852⟩,
⟨64,264501630,264501776⟩]
theorem checked47839 : checkPrefixCuts (2^48) 6274285569 10 Manual.Count131072.C047839.packed 64 cuts47839 = true := by
 decide +kernel
def pointBounds47839 : List (Nat × Nat × Nat) := [(6274318336,111106562515670,111106949323591)]
theorem point_links_checked47839 : (cuts47839.take 1).map (fun c => (6274285569-1+2*2^10*c.k,111106496030853+c.lower,111106882838739+c.upper)) = pointBounds47839 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000244
