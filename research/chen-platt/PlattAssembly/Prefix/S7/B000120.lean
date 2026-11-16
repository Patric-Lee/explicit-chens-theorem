import PlattAssemblyKernel
import PlattCertificates.Count131072.C063840
import PlattCertificates.Count131072.C063841
import PlattCertificates.Count131072.C063842
import PlattCertificates.Count131072.C063843
import PlattCertificates.Count131072.C063844
import PlattCertificates.Count131072.C063845
import PlattCertificates.Count131072.C063846
import PlattCertificates.Count131072.C063847
import PlattCertificates.Count131072.C063848
import PlattCertificates.Count131072.C063849
import PlattCertificates.Count131072.C063850
import PlattCertificates.Count131072.C063851
import PlattCertificates.Count131072.C063852
import PlattCertificates.Count131072.C063853
import PlattCertificates.Count131072.C063854
import PlattCertificates.Count131072.C063855
import PlattCertificates.Count131072.C063856
import PlattCertificates.Count131072.C063857
import PlattCertificates.Count131072.C063858
import PlattCertificates.Count131072.C063859
import PlattCertificates.Count131072.C063860
import PlattCertificates.Count131072.C063861
import PlattCertificates.Count131072.C063862
import PlattCertificates.Count131072.C063863
import PlattCertificates.Count131072.C063864
import PlattCertificates.Count131072.C063865
import PlattCertificates.Count131072.C063866
import PlattCertificates.Count131072.C063867
import PlattCertificates.Count131072.C063868
import PlattCertificates.Count131072.C063869
import PlattCertificates.Count131072.C063870
import PlattCertificates.Count131072.C063871
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63840 : List PrefixCut := [⟨48,143769896,143769979⟩,
⟨64,192051458,192051569⟩]
theorem checked63840 : checkPrefixCuts (2^48) 8371568641 10 Manual.Count131072.C063840.packed 64 cuts63840 = true := by
 decide +kernel
def pointBounds63840 : List (Nat × Nat × Nat) := [(8371666944,114681927802775,114682316648959)]
theorem point_links_checked63840 : (cuts63840.take 1).map (fun c => (8371568641-1+2*2^10*c.k,114681784032879+c.lower,114682172878980+c.upper)) = pointBounds63840 := by
 decide +kernel
def cuts63841 : List PrefixCut := [⟨64,193628680,193628790⟩]
theorem checked63841 : checkPrefixCuts (2^48) 8371699713 10 Manual.Count131072.C063841.packed 64 cuts63841 = true := by
 decide +kernel
def cuts63842 : List PrefixCut := [⟨48,144774047,144774129⟩,
⟨64,191642009,191642115⟩]
theorem checked63842 : checkPrefixCuts (2^48) 8371830785 10 Manual.Count131072.C063842.packed 64 cuts63842 = true := by
 decide +kernel
def pointBounds63842 : List (Nat × Nat × Nat) := [(8371929088,114682314487064,114682703333468)]
theorem point_links_checked63842 : (cuts63842.take 1).map (fun c => (8371830785-1+2*2^10*c.k,114682169713017+c.lower,114682558559339+c.upper)) = pointBounds63842 := by
 decide +kernel
def cuts63843 : List PrefixCut := [⟨64,193286418,193286527⟩]
theorem checked63843 : checkPrefixCuts (2^48) 8371961857 10 Manual.Count131072.C063843.packed 64 cuts63843 = true := by
 decide +kernel
def cuts63844 : List PrefixCut := [⟨48,145878976,145879055⟩,
⟨64,195636800,195636908⟩]
theorem checked63844 : checkPrefixCuts (2^48) 8372092929 10 Manual.Count131072.C063844.packed 64 cuts63844 = true := by
 decide +kernel
def pointBounds63844 : List (Nat × Nat × Nat) := [(8372191232,114682700520420,114683089367036)]
theorem point_links_checked63844 : (cuts63844.take 1).map (fun c => (8372092929-1+2*2^10*c.k,114682554641444+c.lower,114682943487981+c.upper)) = pointBounds63844 := by
 decide +kernel
def cuts63845 : List PrefixCut := [⟨64,193582935,193583044⟩]
theorem checked63845 : checkPrefixCuts (2^48) 8372224001 10 Manual.Count131072.C063845.packed 64 cuts63845 = true := by
 decide +kernel
def cuts63846 : List PrefixCut := [⟨48,147252812,147252895⟩,
⟨64,195899650,195899761⟩]
theorem checked63846 : checkPrefixCuts (2^48) 8372355073 10 Manual.Count131072.C063846.packed 64 cuts63846 = true := by
 decide +kernel
def pointBounds63846 : List (Nat × Nat × Nat) := [(8372453376,114683091113991,114683479960828)]
theorem point_links_checked63846 : (cuts63846.take 1).map (fun c => (8372355073-1+2*2^10*c.k,114682943861179+c.lower,114683332707933+c.upper)) = pointBounds63846 := by
 decide +kernel
def cuts63847 : List PrefixCut := [⟨64,193139841,193139950⟩]
theorem checked63847 : checkPrefixCuts (2^48) 8372486145 10 Manual.Count131072.C063847.packed 64 cuts63847 = true := by
 decide +kernel
def cuts63848 : List PrefixCut := [⟨48,143751890,143751977⟩,
⟨64,192867857,192867973⟩]
theorem checked63848 : checkPrefixCuts (2^48) 8372617217 10 Manual.Count131072.C063848.packed 64 cuts63848 = true := by
 decide +kernel
def pointBounds63848 : List (Nat × Nat × Nat) := [(8372715520,114683476652560,114683865499621)]
theorem point_links_checked63848 : (cuts63848.take 1).map (fun c => (8372617217-1+2*2^10*c.k,114683332900670+c.lower,114683721747644+c.upper)) = pointBounds63848 := by
 decide +kernel
def cuts63849 : List PrefixCut := [⟨64,191183963,191184071⟩]
theorem checked63849 : checkPrefixCuts (2^48) 8372748289 10 Manual.Count131072.C063849.packed 64 cuts63849 = true := by
 decide +kernel
def cuts63850 : List PrefixCut := [⟨48,144587823,144587906⟩,
⟨64,192223104,192223213⟩]
theorem checked63850 : checkPrefixCuts (2^48) 8372879361 10 Manual.Count131072.C063850.packed 64 cuts63850 = true := by
 decide +kernel
def pointBounds63850 : List (Nat × Nat × Nat) := [(8372977664,114683861540313,114684250387594)]
theorem point_links_checked63850 : (cuts63850.take 1).map (fun c => (8372879361-1+2*2^10*c.k,114683716952490+c.lower,114684105799688+c.upper)) = pointBounds63850 := by
 decide +kernel
def cuts63851 : List PrefixCut := [⟨64,193833706,193833815⟩]
theorem checked63851 : checkPrefixCuts (2^48) 8373010433 10 Manual.Count131072.C063851.packed 64 cuts63851 = true := by
 decide +kernel
def cuts63852 : List PrefixCut := [⟨48,143944586,143944667⟩,
⟨64,192418773,192418884⟩]
theorem checked63852 : checkPrefixCuts (2^48) 8373141505 10 Manual.Count131072.C063852.packed 64 cuts63852 = true := by
 decide +kernel
def pointBounds63852 : List (Nat × Nat × Nat) := [(8373239808,114684246953886,114684635801383)]
theorem point_links_checked63852 : (cuts63852.take 1).map (fun c => (8373141505-1+2*2^10*c.k,114684103009300+c.lower,114684491856716+c.upper)) = pointBounds63852 := by
 decide +kernel
def cuts63853 : List PrefixCut := [⟨64,190936684,190936791⟩]
theorem checked63853 : checkPrefixCuts (2^48) 8373272577 10 Manual.Count131072.C063853.packed 64 cuts63853 = true := by
 decide +kernel
def cuts63854 : List PrefixCut := [⟨48,143772006,143772092⟩,
⟨64,192547211,192547327⟩]
theorem checked63854 : checkPrefixCuts (2^48) 8373403649 10 Manual.Count131072.C063854.packed 64 cuts63854 = true := by
 decide +kernel
def pointBounds63854 : List (Nat × Nat × Nat) := [(8373501952,114684630136763,114685018984483)]
theorem point_links_checked63854 : (cuts63854.take 1).map (fun c => (8373403649-1+2*2^10*c.k,114684486364757+c.lower,114684875212391+c.upper)) = pointBounds63854 := by
 decide +kernel
def cuts63855 : List PrefixCut := [⟨64,194325783,194325886⟩]
theorem checked63855 : checkPrefixCuts (2^48) 8373534721 10 Manual.Count131072.C063855.packed 64 cuts63855 = true := by
 decide +kernel
def cuts63856 : List PrefixCut := [⟨48,143633064,143633143⟩,
⟨64,191902532,191902641⟩]
theorem checked63856 : checkPrefixCuts (2^48) 8373665793 10 Manual.Count131072.C063856.packed 64 cuts63856 = true := by
 decide +kernel
def pointBounds63856 : List (Nat × Nat × Nat) := [(8373764096,114685016870815,114685405718747)]
theorem point_links_checked63856 : (cuts63856.take 1).map (fun c => (8373665793-1+2*2^10*c.k,114684873237751+c.lower,114685262085604+c.upper)) = pointBounds63856 := by
 decide +kernel
def cuts63857 : List PrefixCut := [⟨64,190655821,190655937⟩]
theorem checked63857 : checkPrefixCuts (2^48) 8373796865 10 Manual.Count131072.C063857.packed 64 cuts63857 = true := by
 decide +kernel
def cuts63858 : List PrefixCut := [⟨48,141981507,141981590⟩,
⟨64,190888108,190888220⟩]
theorem checked63858 : checkPrefixCuts (2^48) 8373927937 10 Manual.Count131072.C063858.packed 64 cuts63858 = true := by
 decide +kernel
def pointBounds63858 : List (Nat × Nat × Nat) := [(8374026240,114685397777611,114685786625772)]
theorem point_links_checked63858 : (cuts63858.take 1).map (fun c => (8373927937-1+2*2^10*c.k,114685255796104+c.lower,114685644644182+c.upper)) = pointBounds63858 := by
 decide +kernel
def cuts63859 : List PrefixCut := [⟨64,189742326,189742431⟩]
theorem checked63859 : checkPrefixCuts (2^48) 8374059009 10 Manual.Count131072.C063859.packed 64 cuts63859 = true := by
 decide +kernel
def cuts63860 : List PrefixCut := [⟨48,145808846,145808926⟩,
⟨64,194176130,194176236⟩]
theorem checked63860 : checkPrefixCuts (2^48) 8374190081 10 Manual.Count131072.C063860.packed 64 cuts63860 = true := by
 decide +kernel
def pointBounds63860 : List (Nat × Nat × Nat) := [(8374288384,114685782235384,114686171083759)]
theorem point_links_checked63860 : (cuts63860.take 1).map (fun c => (8374190081-1+2*2^10*c.k,114685636426538+c.lower,114686025274833+c.upper)) = pointBounds63860 := by
 decide +kernel
def cuts63861 : List PrefixCut := [⟨64,195584757,195584868⟩]
theorem checked63861 : checkPrefixCuts (2^48) 8374321153 10 Manual.Count131072.C063861.packed 64 cuts63861 = true := by
 decide +kernel
def cuts63862 : List PrefixCut := [⟨48,143821229,143821310⟩,
⟨64,193665868,193665979⟩]
theorem checked63862 : checkPrefixCuts (2^48) 8374452225 10 Manual.Count131072.C063862.packed 64 cuts63862 = true := by
 decide +kernel
def pointBounds63862 : List (Nat × Nat × Nat) := [(8374550528,114686170008654,114686558857247)]
theorem point_links_checked63862 : (cuts63862.take 1).map (fun c => (8374452225-1+2*2^10*c.k,114686026187425+c.lower,114686415035937+c.upper)) = pointBounds63862 := by
 decide +kernel
def cuts63863 : List PrefixCut := [⟨64,192957031,192957141⟩]
theorem checked63863 : checkPrefixCuts (2^48) 8374583297 10 Manual.Count131072.C063863.packed 64 cuts63863 = true := by
 decide +kernel
def cuts63864 : List PrefixCut := [⟨48,144656976,144657063⟩,
⟨64,192080162,192080277⟩]
theorem checked63864 : checkPrefixCuts (2^48) 8374714369 10 Manual.Count131072.C063864.packed 64 cuts63864 = true := by
 decide +kernel
def pointBounds63864 : List (Nat × Nat × Nat) := [(8374812672,114686557467300,114686946316120)]
theorem point_links_checked63864 : (cuts63864.take 1).map (fun c => (8374714369-1+2*2^10*c.k,114686412810324+c.lower,114686801659057+c.upper)) = pointBounds63864 := by
 decide +kernel
def cuts63865 : List PrefixCut := [⟨64,193320705,193320819⟩]
theorem checked63865 : checkPrefixCuts (2^48) 8374845441 10 Manual.Count131072.C063865.packed 64 cuts63865 = true := by
 decide +kernel
def cuts63866 : List PrefixCut := [⟨48,143106445,143106531⟩,
⟨64,192947962,192948078⟩]
theorem checked63866 : checkPrefixCuts (2^48) 8374976513 10 Manual.Count131072.C063866.packed 64 cuts63866 = true := by
 decide +kernel
def pointBounds63866 : List (Nat × Nat × Nat) := [(8375074816,114686941317636,114687330166684)]
theorem point_links_checked63866 : (cuts63866.take 1).map (fun c => (8374976513-1+2*2^10*c.k,114686798211191+c.lower,114687187060153+c.upper)) = pointBounds63866 := by
 decide +kernel
def cuts63867 : List PrefixCut := [⟨64,194591751,194591868⟩]
theorem checked63867 : checkPrefixCuts (2^48) 8375107585 10 Manual.Count131072.C063867.packed 64 cuts63867 = true := by
 decide +kernel
def cuts63868 : List PrefixCut := [⟨48,143807726,143807809⟩,
⟨64,192202564,192202678⟩]
theorem checked63868 : checkPrefixCuts (2^48) 8375238657 10 Manual.Count131072.C063868.packed 64 cuts63868 = true := by
 decide +kernel
def pointBounds63868 : List (Nat × Nat × Nat) := [(8375336960,114687329558630,114687718407908)]
theorem point_links_checked63868 : (cuts63868.take 1).map (fun c => (8375238657-1+2*2^10*c.k,114687185750904+c.lower,114687574600099+c.upper)) = pointBounds63868 := by
 decide +kernel
def cuts63869 : List PrefixCut := [⟨64,194316804,194316918⟩]
theorem checked63869 : checkPrefixCuts (2^48) 8375369729 10 Manual.Count131072.C063869.packed 64 cuts63869 = true := by
 decide +kernel
def cuts63870 : List PrefixCut := [⟨48,143433554,143433638⟩,
⟨64,190583433,190583548⟩]
theorem checked63870 : checkPrefixCuts (2^48) 8375500801 10 Manual.Count131072.C063870.packed 64 cuts63870 = true := by
 decide +kernel
def pointBounds63870 : List (Nat × Nat × Nat) := [(8375599104,114687715703826,114688104553333)]
theorem point_links_checked63870 : (cuts63870.take 1).map (fun c => (8375500801-1+2*2^10*c.k,114687572270272+c.lower,114687961119695+c.upper)) = pointBounds63870 := by
 decide +kernel
def cuts63871 : List PrefixCut := [⟨64,193840250,193840357⟩]
theorem checked63871 : checkPrefixCuts (2^48) 8375631873 10 Manual.Count131072.C063871.packed 64 cuts63871 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000120
