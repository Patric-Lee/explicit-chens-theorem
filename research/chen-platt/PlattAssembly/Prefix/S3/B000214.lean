import PlattAssemblyKernel
import PlattCertificates.Count131072.C026848
import PlattCertificates.Count131072.C026849
import PlattCertificates.Count131072.C026850
import PlattCertificates.Count131072.C026851
import PlattCertificates.Count131072.C026852
import PlattCertificates.Count131072.C026853
import PlattCertificates.Count131072.C026854
import PlattCertificates.Count131072.C026855
import PlattCertificates.Count131072.C026856
import PlattCertificates.Count131072.C026857
import PlattCertificates.Count131072.C026858
import PlattCertificates.Count131072.C026859
import PlattCertificates.Count131072.C026860
import PlattCertificates.Count131072.C026861
import PlattCertificates.Count131072.C026862
import PlattCertificates.Count131072.C026863
import PlattCertificates.Count131072.C026864
import PlattCertificates.Count131072.C026865
import PlattCertificates.Count131072.C026866
import PlattCertificates.Count131072.C026867
import PlattCertificates.Count131072.C026868
import PlattCertificates.Count131072.C026869
import PlattCertificates.Count131072.C026870
import PlattCertificates.Count131072.C026871
import PlattCertificates.Count131072.C026872
import PlattCertificates.Count131072.C026873
import PlattCertificates.Count131072.C026874
import PlattCertificates.Count131072.C026875
import PlattCertificates.Count131072.C026876
import PlattCertificates.Count131072.C026877
import PlattCertificates.Count131072.C026878
import PlattCertificates.Count131072.C026879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000214
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26848 : List PrefixCut := [⟨24,87167791,87167838⟩,
⟨128,472744263,472744527⟩]
theorem checked26848 : checkPrefixCuts (2^48) 3522953217 9 Manual.Count131072.C026848.packed 128 cuts26848 = true := by
 decide +kernel
def pointBounds26848 : List (Nat × Nat × Nat) := [(3522977792,103811738331840,103812120859902)]
theorem point_links_checked26848 : (cuts26848.take 1).map (fun c => (3522953217-1+2*2^9*c.k,103811651164049+c.lower,103812033692064+c.upper)) = pointBounds26848 := by
 decide +kernel
def cuts26849 : List PrefixCut := [⟨4,14940254,14940264⟩,
⟨112,415204718,415204956⟩,
⟨128,474084876,474085145⟩]
theorem checked26849 : checkPrefixCuts (2^48) 3523084289 9 Manual.Count131072.C026849.packed 128 cuts26849 = true := by
 decide +kernel
def pointBounds26849 : List (Nat × Nat × Nat) := [(3523088384,103812138848566,103812521376855),(3523198976,103812539113030,103812921641547)]
theorem point_links_checked26849 : (cuts26849.take 2).map (fun c => (3523084289-1+2*2^9*c.k,103812123908312+c.lower,103812506436591+c.upper)) = pointBounds26849 := by
 decide +kernel
def cuts26850 : List PrefixCut := [⟨92,344167878,344168072⟩,
⟨128,473028729,473028997⟩]
theorem checked26850 : checkPrefixCuts (2^48) 3523215361 9 Manual.Count131072.C026850.packed 128 cuts26850 = true := by
 decide +kernel
def pointBounds26850 : List (Nat × Nat × Nat) := [(3523309568,103812942161066,103813324689808)]
theorem point_links_checked26850 : (cuts26850.take 1).map (fun c => (3523215361-1+2*2^9*c.k,103812597993188+c.lower,103812980521736+c.upper)) = pointBounds26850 := by
 decide +kernel
def cuts26851 : List PrefixCut := [⟨72,272656620,272656773⟩,
⟨128,479801512,479801779⟩]
theorem checked26851 : checkPrefixCuts (2^48) 3523346433 9 Manual.Count131072.C026851.packed 128 cuts26851 = true := by
 decide +kernel
def pointBounds26851 : List (Nat × Nat × Nat) := [(3523420160,103813343678537,103813726207506)]
theorem point_links_checked26851 : (cuts26851.take 1).map (fun c => (3523346433-1+2*2^9*c.k,103813071021917+c.lower,103813453550733+c.upper)) = pointBounds26851 := by
 decide +kernel
def cuts26852 : List PrefixCut := [⟨52,196836471,196836582⟩,
⟨128,480422714,480422986⟩]
theorem checked26852 : checkPrefixCuts (2^48) 3523477505 9 Manual.Count131072.C026852.packed 128 cuts26852 = true := by
 decide +kernel
def pointBounds26852 : List (Nat × Nat × Nat) := [(3523530752,103813747659900,103814130189094)]
theorem point_links_checked26852 : (cuts26852.take 1).map (fun c => (3523477505-1+2*2^9*c.k,103813550823429+c.lower,103813933352512+c.upper)) = pointBounds26852 := by
 decide +kernel
def cuts26853 : List PrefixCut := [⟨32,120142812,120142882⟩,
⟨128,477049799,477050069⟩]
theorem checked26853 : checkPrefixCuts (2^48) 3523608577 9 Manual.Count131072.C026853.packed 128 cuts26853 = true := by
 decide +kernel
def pointBounds26853 : List (Nat × Nat × Nat) := [(3523641344,103814151388955,103814533918380)]
theorem point_links_checked26853 : (cuts26853.take 1).map (fun c => (3523608577-1+2*2^9*c.k,103814031246143+c.lower,103814413775498+c.upper)) = pointBounds26853 := by
 decide +kernel
def cuts26854 : List PrefixCut := [⟨12,45611173,45611198⟩,
⟨120,446519227,446519476⟩,
⟨128,476233364,476233631⟩]
theorem checked26854 : checkPrefixCuts (2^48) 3523739649 9 Manual.Count131072.C026854.packed 128 cuts26854 = true := by
 decide +kernel
def pointBounds26854 : List (Nat × Nat × Nat) := [(3523751936,103814553907115,103814936436765),(3523862528,103814954815169,103815337345043)]
theorem point_links_checked26854 : (cuts26854.take 2).map (fun c => (3523739649-1+2*2^9*c.k,103814508295942+c.lower,103814890825567+c.upper)) = pointBounds26854 := by
 decide +kernel
def cuts26855 : List PrefixCut := [⟨100,372698957,372699163⟩,
⟨128,478452100,478452363⟩]
theorem checked26855 : checkPrefixCuts (2^48) 3523870721 9 Manual.Count131072.C026855.packed 128 cuts26855 = true := by
 decide +kernel
def pointBounds26855 : List (Nat × Nat × Nat) := [(3523973120,103815357228263,103815739758361)]
theorem point_links_checked26855 : (cuts26855.take 1).map (fun c => (3523870721-1+2*2^9*c.k,103814984529306+c.lower,103815367059198+c.upper)) = pointBounds26855 := by
 decide +kernel
def cuts26856 : List PrefixCut := [⟨80,301120146,301120314⟩,
⟨128,477715459,477715725⟩]
theorem checked26856 : checkPrefixCuts (2^48) 3524001793 9 Manual.Count131072.C026856.packed 128 cuts26856 = true := by
 decide +kernel
def pointBounds26856 : List (Nat × Nat × Nat) := [(3524083712,103815764101552,103816146631875)]
theorem point_links_checked26856 : (cuts26856.take 1).map (fun c => (3524001793-1+2*2^9*c.k,103815462981406+c.lower,103815845511561+c.upper)) = pointBounds26856 := by
 decide +kernel
def cuts26857 : List PrefixCut := [⟨60,222997024,222997152⟩,
⟨128,473784092,473784361⟩]
theorem checked26857 : checkPrefixCuts (2^48) 3524132865 9 Manual.Count131072.C026857.packed 128 cuts26857 = true := by
 decide +kernel
def pointBounds26857 : List (Nat × Nat × Nat) := [(3524194304,103816163693889,103816546224438)]
theorem point_links_checked26857 : (cuts26857.take 1).map (fun c => (3524132865-1+2*2^9*c.k,103815940696865+c.lower,103816323227286+c.upper)) = pointBounds26857 := by
 decide +kernel
def cuts26858 : List PrefixCut := [⟨40,148313458,148313542⟩,
⟨128,474485198,474485468⟩]
theorem checked26858 : checkPrefixCuts (2^48) 3524263937 9 Manual.Count131072.C026858.packed 128 cuts26858 = true := by
 decide +kernel
def pointBounds26858 : List (Nat × Nat × Nat) := [(3524304896,103816562794415,103816945325189)]
theorem point_links_checked26858 : (cuts26858.take 1).map (fun c => (3524263937-1+2*2^9*c.k,103816414480957+c.lower,103816797011647+c.upper)) = pointBounds26858 := by
 decide +kernel
def cuts26859 : List PrefixCut := [⟨20,75471956,75471997⟩,
⟨128,479179574,479179842⟩]
theorem checked26859 : checkPrefixCuts (2^48) 3524395009 9 Manual.Count131072.C026859.packed 128 cuts26859 = true := by
 decide +kernel
def pointBounds26859 : List (Nat × Nat × Nat) := [(3524415488,103816964438111,103817346969112),(3524526080,103817368145729,103817750676957)]
theorem point_links_checked26859 : (cuts26859.take 2).map (fun c => (3524395009-1+2*2^9*c.k,103816888966155+c.lower,103817271497115+c.upper)) = pointBounds26859 := by
 decide +kernel
def cuts26860 : List PrefixCut := [⟨108,398903241,398903463⟩,
⟨128,474609611,474609874⟩]
theorem checked26860 : checkPrefixCuts (2^48) 3524526081 9 Manual.Count131072.C026860.packed 128 cuts26860 = true := by
 decide +kernel
def pointBounds26860 : List (Nat × Nat × Nat) := [(3524636672,103817767048970,103818149580420)]
theorem point_links_checked26860 : (cuts26860.take 1).map (fun c => (3524526081-1+2*2^9*c.k,103817368145729+c.lower,103817750676957+c.upper)) = pointBounds26860 := by
 decide +kernel
def cuts26861 : List PrefixCut := [⟨88,326219019,326219207⟩,
⟨128,477386980,477387252⟩]
theorem checked26861 : checkPrefixCuts (2^48) 3524657153 9 Manual.Count131072.C026861.packed 128 cuts26861 = true := by
 decide +kernel
def pointBounds26861 : List (Nat × Nat × Nat) := [(3524747264,103818168974359,103818551506038)]
theorem point_links_checked26861 : (cuts26861.take 1).map (fun c => (3524657153-1+2*2^9*c.k,103817842755340+c.lower,103818225286831+c.upper)) = pointBounds26861 := by
 decide +kernel
def cuts26862 : List PrefixCut := [⟨68,252741186,252741331⟩,
⟨128,475852039,475852309⟩]
theorem checked26862 : checkPrefixCuts (2^48) 3524788225 9 Manual.Count131072.C026862.packed 128 cuts26862 = true := by
 decide +kernel
def pointBounds26862 : List (Nat × Nat × Nat) := [(3524857856,103818572883506,103818955415414)]
theorem point_links_checked26862 : (cuts26862.take 1).map (fun c => (3524788225-1+2*2^9*c.k,103818320142320+c.lower,103818702674083+c.upper)) = pointBounds26862 := by
 decide +kernel
def cuts26863 : List PrefixCut := [⟨48,181823683,181823781⟩,
⟨128,477431434,477431697⟩]
theorem checked26863 : checkPrefixCuts (2^48) 3524919297 9 Manual.Count131072.C026863.packed 128 cuts26863 = true := by
 decide +kernel
def pointBounds26863 : List (Nat × Nat × Nat) := [(3524968448,103818977818042,103819360350173)]
theorem point_links_checked26863 : (cuts26863.take 1).map (fun c => (3524919297-1+2*2^9*c.k,103818795994359+c.lower,103819178526392+c.upper)) = pointBounds26863 := by
 decide +kernel
def cuts26864 : List PrefixCut := [⟨28,105321583,105321641⟩,
⟨128,480687366,480687631⟩]
theorem checked26864 : checkPrefixCuts (2^48) 3525050369 9 Manual.Count131072.C026864.packed 128 cuts26864 = true := by
 decide +kernel
def pointBounds26864 : List (Nat × Nat × Nat) := [(3525079040,103819378747376,103819761279730)]
theorem point_links_checked26864 : (cuts26864.take 1).map (fun c => (3525050369-1+2*2^9*c.k,103819273425793+c.lower,103819655958089+c.upper)) = pointBounds26864 := by
 decide +kernel
def cuts26865 : List PrefixCut := [⟨8,29623175,29623191⟩,
⟨116,434439843,434440078⟩,
⟨128,477795189,477795447⟩]
theorem checked26865 : checkPrefixCuts (2^48) 3525181441 9 Manual.Count131072.C026865.packed 128 cuts26865 = true := by
 decide +kernel
def pointBounds26865 : List (Nat × Nat × Nat) := [(3525189632,103819783736334,103820166268911),(3525300224,103820188553002,103820571085798)]
theorem point_links_checked26865 : (cuts26865.take 2).map (fun c => (3525181441-1+2*2^9*c.k,103819754113159+c.lower,103820136645720+c.upper)) = pointBounds26865 := by
 decide +kernel
def cuts26866 : List PrefixCut := [⟨96,358095178,358095376⟩,
⟨128,478495942,478496209⟩]
theorem checked26866 : checkPrefixCuts (2^48) 3525312513 9 Manual.Count131072.C026866.packed 128 cuts26866 = true := by
 decide +kernel
def pointBounds26866 : List (Nat × Nat × Nat) := [(3525410816,103820590003526,103820972536543)]
theorem point_links_checked26866 : (cuts26866.take 1).map (fun c => (3525312513-1+2*2^9*c.k,103820231908348+c.lower,103820614441167+c.upper)) = pointBounds26866 := by
 decide +kernel
def cuts26867 : List PrefixCut := [⟨76,281196872,281197032⟩,
⟨128,475763605,475763875⟩]
theorem checked26867 : checkPrefixCuts (2^48) 3525443585 9 Manual.Count131072.C026867.packed 128 cuts26867 = true := by
 decide +kernel
def pointBounds26867 : List (Nat × Nat × Nat) := [(3525521408,103820991601162,103821374134408)]
theorem point_links_checked26867 : (cuts26867.take 1).map (fun c => (3525443585-1+2*2^9*c.k,103820710404290+c.lower,103821092937376+c.upper)) = pointBounds26867 := by
 decide +kernel
def cuts26868 : List PrefixCut := [⟨56,208774728,208774844⟩,
⟨128,471195265,471195527⟩]
theorem checked26868 : checkPrefixCuts (2^48) 3525574657 9 Manual.Count131072.C026868.packed 128 cuts26868 = true := by
 decide +kernel
def pointBounds26868 : List (Nat × Nat × Nat) := [(3525632000,103821394942623,103821777476095)]
theorem point_links_checked26868 : (cuts26868.take 1).map (fun c => (3525574657-1+2*2^9*c.k,103821186167895+c.lower,103821568701251+c.upper)) = pointBounds26868 := by
 decide +kernel
def cuts26869 : List PrefixCut := [⟨36,137794578,137794653⟩,
⟨128,476526590,476526854⟩]
theorem checked26869 : checkPrefixCuts (2^48) 3525705729 9 Manual.Count131072.C026869.packed 128 cuts26869 = true := by
 decide +kernel
def pointBounds26869 : List (Nat × Nat × Nat) := [(3525742592,103821795157738,103822177691431)]
theorem point_links_checked26869 : (cuts26869.take 1).map (fun c => (3525705729-1+2*2^9*c.k,103821657363160+c.lower,103822039896778+c.upper)) = pointBounds26869 := by
 decide +kernel
def cuts26870 : List PrefixCut := [⟨16,58436949,58436981⟩,
⟨124,465492496,465492758⟩,
⟨128,480660037,480660307⟩]
theorem checked26870 : checkPrefixCuts (2^48) 3525836801 9 Manual.Count131072.C026870.packed 128 cuts26870 = true := by
 decide +kernel
def pointBounds26870 : List (Nat × Nat × Nat) := [(3525853184,103822192326699,103822574860613),(3525963776,103822599382246,103822981916390)]
theorem point_links_checked26870 : (cuts26870.take 2).map (fun c => (3525836801-1+2*2^9*c.k,103822133889750+c.lower,103822516423632+c.upper)) = pointBounds26870 := by
 decide +kernel
def cuts26871 : List PrefixCut := [⟨104,385648637,385648856⟩,
⟨128,474575279,474575548⟩]
theorem checked26871 : checkPrefixCuts (2^48) 3525967873 9 Manual.Count131072.C026871.packed 128 cuts26871 = true := by
 decide +kernel
def pointBounds26871 : List (Nat × Nat × Nat) := [(3526074368,103823000198424,103823382732795)]
theorem point_links_checked26871 : (cuts26871.take 1).map (fun c => (3525967873-1+2*2^9*c.k,103822614549787+c.lower,103822997083939+c.upper)) = pointBounds26871 := by
 decide +kernel
def cuts26872 : List PrefixCut := [⟨84,309881311,309881486⟩,
⟨128,469369062,469369331⟩]
theorem checked26872 : checkPrefixCuts (2^48) 3526098945 9 Manual.Count131072.C026872.packed 128 cuts26872 = true := by
 decide +kernel
def pointBounds26872 : List (Nat × Nat × Nat) := [(3526184960,103823399006377,103823781540973)]
theorem point_links_checked26872 : (cuts26872.take 1).map (fun c => (3526098945-1+2*2^9*c.k,103823089125066+c.lower,103823471659487+c.upper)) = pointBounds26872 := by
 decide +kernel
def cuts26873 : List PrefixCut := [⟨64,238748935,238749067⟩,
⟨128,481484486,481484753⟩]
theorem checked26873 : checkPrefixCuts (2^48) 3526230017 9 Manual.Count131072.C026873.packed 128 cuts26873 = true := by
 decide +kernel
def pointBounds26873 : List (Nat × Nat × Nat) := [(3526295552,103823797243063,103824179777885)]
theorem point_links_checked26873 : (cuts26873.take 1).map (fun c => (3526230017-1+2*2^9*c.k,103823558494128+c.lower,103823941028818+c.upper)) = pointBounds26873 := by
 decide +kernel
def cuts26874 : List PrefixCut := [⟨44,163311116,163311209⟩,
⟨128,474442571,474442836⟩]
theorem checked26874 : checkPrefixCuts (2^48) 3526361089 9 Manual.Count131072.C026874.packed 128 cuts26874 = true := by
 decide +kernel
def pointBounds26874 : List (Nat × Nat × Nat) := [(3526406144,103824203289730,103824585824780)]
theorem point_links_checked26874 : (cuts26874.take 1).map (fun c => (3526361089-1+2*2^9*c.k,103824039978614+c.lower,103824422513571+c.upper)) = pointBounds26874 := by
 decide +kernel
def cuts26875 : List PrefixCut := [⟨24,87160132,87160180⟩,
⟨128,474823993,474824257⟩]
theorem checked26875 : checkPrefixCuts (2^48) 3526492161 9 Manual.Count131072.C026875.packed 128 cuts26875 = true := by
 decide +kernel
def pointBounds26875 : List (Nat × Nat × Nat) := [(3526516736,103824601581317,103824984116587)]
theorem point_links_checked26875 : (cuts26875.take 1).map (fun c => (3526492161-1+2*2^9*c.k,103824514421185+c.lower,103824896956407+c.upper)) = pointBounds26875 := by
 decide +kernel
def cuts26876 : List PrefixCut := [⟨4,13488606,13488614⟩,
⟨112,415027450,415027686⟩,
⟨128,476721739,476722009⟩]
theorem checked26876 : checkPrefixCuts (2^48) 3526623233 9 Manual.Count131072.C026876.packed 128 cuts26876 = true := by
 decide +kernel
def pointBounds26876 : List (Nat × Nat × Nat) := [(3526627328,103825002733784,103825385269278),(3526737920,103825404272628,103825786808350)]
theorem point_links_checked26876 : (cuts26876.take 2).map (fun c => (3526623233-1+2*2^9*c.k,103824989245178+c.lower,103825371780664+c.upper)) = pointBounds26876 := by
 decide +kernel
def cuts26877 : List PrefixCut := [⟨92,343583130,343583323⟩,
⟨128,477262813,477263081⟩]
theorem checked26877 : checkPrefixCuts (2^48) 3526754305 9 Manual.Count131072.C026877.packed 128 cuts26877 = true := by
 decide +kernel
def pointBounds26877 : List (Nat × Nat × Nat) := [(3526848512,103825809550047,103826192085996)]
theorem point_links_checked26877 : (cuts26877.take 1).map (fun c => (3526754305-1+2*2^9*c.k,103825465966917+c.lower,103825848502673+c.upper)) = pointBounds26877 := by
 decide +kernel
def cuts26878 : List PrefixCut := [⟨72,270866738,270866887⟩,
⟨128,480517193,480517458⟩]
theorem checked26878 : checkPrefixCuts (2^48) 3526885377 9 Manual.Count131072.C026878.packed 128 cuts26878 = true := by
 decide +kernel
def pointBounds26878 : List (Nat × Nat × Nat) := [(3526959104,103826214096468,103826596632641)]
theorem point_links_checked26878 : (cuts26878.take 1).map (fun c => (3526885377-1+2*2^9*c.k,103825943229730+c.lower,103826325765754+c.upper)) = pointBounds26878 := by
 decide +kernel
def cuts26879 : List PrefixCut := [⟨52,193366999,193367108⟩,
⟨128,477945556,477945822⟩]
theorem checked26879 : checkPrefixCuts (2^48) 3527016449 9 Manual.Count131072.C026879.packed 128 cuts26879 = true := by
 decide +kernel
def pointBounds26879 : List (Nat × Nat × Nat) := [(3527069696,103826617113922,103826999650320)]
theorem point_links_checked26879 : (cuts26879.take 1).map (fun c => (3527016449-1+2*2^9*c.k,103826423746923+c.lower,103826806283212+c.upper)) = pointBounds26879 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000214
