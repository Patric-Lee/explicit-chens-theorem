import PlattAssemblyKernel
import PlattCertificates.Count131072.C067904
import PlattCertificates.Count131072.C067905
import PlattCertificates.Count131072.C067906
import PlattCertificates.Count131072.C067907
import PlattCertificates.Count131072.C067908
import PlattCertificates.Count131072.C067909
import PlattCertificates.Count131072.C067910
import PlattCertificates.Count131072.C067911
import PlattCertificates.Count131072.C067912
import PlattCertificates.Count131072.C067913
import PlattCertificates.Count131072.C067914
import PlattCertificates.Count131072.C067915
import PlattCertificates.Count131072.C067916
import PlattCertificates.Count131072.C067917
import PlattCertificates.Count131072.C067918
import PlattCertificates.Count131072.C067919
import PlattCertificates.Count131072.C067920
import PlattCertificates.Count131072.C067921
import PlattCertificates.Count131072.C067922
import PlattCertificates.Count131072.C067923
import PlattCertificates.Count131072.C067924
import PlattCertificates.Count131072.C067925
import PlattCertificates.Count131072.C067926
import PlattCertificates.Count131072.C067927
import PlattCertificates.Count131072.C067928
import PlattCertificates.Count131072.C067929
import PlattCertificates.Count131072.C067930
import PlattCertificates.Count131072.C067931
import PlattCertificates.Count131072.C067932
import PlattCertificates.Count131072.C067933
import PlattCertificates.Count131072.C067934
import PlattCertificates.Count131072.C067935
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000247
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67904 : List PrefixCut := [⟨64,182206272,182206381⟩]
theorem checked67904 : checkPrefixCuts (2^48) 8904245249 10 Manual.Count131072.C067904.packed 64 cuts67904 = true := by
 decide +kernel
def cuts67905 : List PrefixCut := [⟨37,102608376,102608438⟩,
⟨64,177872931,177873042⟩]
theorem checked67905 : checkPrefixCuts (2^48) 8904376321 10 Manual.Count131072.C067905.packed 64 cuts67905 = true := by
 decide +kernel
def pointBounds67905 : List (Nat × Nat × Nat) := [(8904452096,115440937751412,115441327038007)]
theorem point_links_checked67905 : (cuts67905.take 1).map (fun c => (8904376321-1+2*2^10*c.k,115440835143036+c.lower,115441224429569+c.upper)) = pointBounds67905 := by
 decide +kernel
def cuts67906 : List PrefixCut := [⟨64,181347433,181347544⟩]
theorem checked67906 : checkPrefixCuts (2^48) 8904507393 10 Manual.Count131072.C067906.packed 64 cuts67906 = true := by
 decide +kernel
def cuts67907 : List PrefixCut := [⟨45,128525266,128525346⟩,
⟨64,182040187,182040299⟩]
theorem checked67907 : checkPrefixCuts (2^48) 8904638465 10 Manual.Count131072.C067907.packed 64 cuts67907 = true := by
 decide +kernel
def pointBounds67907 : List (Nat × Nat × Nat) := [(8904730624,115441322888666,115441712175501)]
theorem point_links_checked67907 : (cuts67907.take 1).map (fun c => (8904638465-1+2*2^10*c.k,115441194363400+c.lower,115441583650155+c.upper)) = pointBounds67907 := by
 decide +kernel
def cuts67908 : List PrefixCut := [⟨64,179666816,179666919⟩]
theorem checked67908 : checkPrefixCuts (2^48) 8904769537 10 Manual.Count131072.C067908.packed 64 cuts67908 = true := by
 decide +kernel
def cuts67909 : List PrefixCut := [⟨53,149857291,149857383⟩,
⟨64,180675638,180675748⟩]
theorem checked67909 : checkPrefixCuts (2^48) 8904900609 10 Manual.Count131072.C067909.packed 64 cuts67909 = true := by
 decide +kernel
def pointBounds67909 : List (Nat × Nat × Nat) := [(8905009152,115441705927694,115442095214756)]
theorem point_links_checked67909 : (cuts67909.take 1).map (fun c => (8904900609-1+2*2^10*c.k,115441556070403+c.lower,115441945357373+c.upper)) = pointBounds67909 := by
 decide +kernel
def cuts67910 : List PrefixCut := [⟨64,181273533,181273638⟩]
theorem checked67910 : checkPrefixCuts (2^48) 8905031681 10 Manual.Count131072.C067910.packed 64 cuts67910 = true := by
 decide +kernel
def cuts67911 : List PrefixCut := [⟨61,177762464,177762565⟩,
⟨64,186201693,186201800⟩]
theorem checked67911 : checkPrefixCuts (2^48) 8905162753 10 Manual.Count131072.C067911.packed 64 cuts67911 = true := by
 decide +kernel
def pointBounds67911 : List (Nat × Nat × Nat) := [(8905287680,115442095782038,115442485069324)]
theorem point_links_checked67911 : (cuts67911.take 1).map (fun c => (8905162753-1+2*2^10*c.k,115441918019574+c.lower,115442307306759+c.upper)) = pointBounds67911 := by
 decide +kernel
def cuts67912 : List PrefixCut := [⟨64,179118898,179119001⟩]
theorem checked67912 : checkPrefixCuts (2^48) 8905293825 10 Manual.Count131072.C067912.packed 64 cuts67912 = true := by
 decide +kernel
def cuts67913 : List PrefixCut := [⟨64,179780022,179780129⟩]
theorem checked67913 : checkPrefixCuts (2^48) 8905424897 10 Manual.Count131072.C067913.packed 64 cuts67913 = true := by
 decide +kernel
def cuts67914 : List PrefixCut := [⟨5,14444236,14444244⟩,
⟨64,181231263,181231368⟩]
theorem checked67914 : checkPrefixCuts (2^48) 8905555969 10 Manual.Count131072.C067914.packed 64 cuts67914 = true := by
 decide +kernel
def pointBounds67914 : List (Nat × Nat × Nat) := [(8905566208,115442477564423,115442866851933)]
theorem point_links_checked67914 : (cuts67914.take 1).map (fun c => (8905555969-1+2*2^10*c.k,115442463120187+c.lower,115442852407689+c.upper)) = pointBounds67914 := by
 decide +kernel
def cuts67915 : List PrefixCut := [⟨64,181449824,181449929⟩]
theorem checked67915 : checkPrefixCuts (2^48) 8905687041 10 Manual.Count131072.C067915.packed 64 cuts67915 = true := by
 decide +kernel
def cuts67916 : List PrefixCut := [⟨13,36251718,36251741⟩,
⟨64,182521744,182521851⟩]
theorem checked67916 : checkPrefixCuts (2^48) 8905818113 10 Manual.Count131072.C067916.packed 64 cuts67916 = true := by
 decide +kernel
def pointBounds67916 : List (Nat × Nat × Nat) := [(8905844736,115442862052992,115443251340727)]
theorem point_links_checked67916 : (cuts67916.take 1).map (fun c => (8905818113-1+2*2^10*c.k,115442825801274+c.lower,115443215088986+c.upper)) = pointBounds67916 := by
 decide +kernel
def cuts67917 : List PrefixCut := [⟨64,174965468,174965568⟩]
theorem checked67917 : checkPrefixCuts (2^48) 8905949185 10 Manual.Count131072.C067917.packed 64 cuts67917 = true := by
 decide +kernel
def cuts67918 : List PrefixCut := [⟨21,59132436,59132473⟩,
⟨64,181947496,181947607⟩]
theorem checked67918 : checkPrefixCuts (2^48) 8906080257 10 Manual.Count131072.C067918.packed 64 cuts67918 = true := by
 decide +kernel
def pointBounds67918 : List (Nat × Nat × Nat) := [(8906123264,115443242420922,115443631708878)]
theorem point_links_checked67918 : (cuts67918.take 1).map (fun c => (8906080257-1+2*2^10*c.k,115443183288486+c.lower,115443572576405+c.upper)) = pointBounds67918 := by
 decide +kernel
def cuts67919 : List PrefixCut := [⟨64,180933489,180933598⟩]
theorem checked67919 : checkPrefixCuts (2^48) 8906211329 10 Manual.Count131072.C067919.packed 64 cuts67919 = true := by
 decide +kernel
def cuts67920 : List PrefixCut := [⟨29,82201393,82201439⟩,
⟨64,179413860,179413962⟩]
theorem checked67920 : checkPrefixCuts (2^48) 8906342401 10 Manual.Count131072.C067920.packed 64 cuts67920 = true := by
 decide +kernel
def pointBounds67920 : List (Nat × Nat × Nat) := [(8906401792,115443628370864,115444017659049)]
theorem point_links_checked67920 : (cuts67920.take 1).map (fun c => (8906342401-1+2*2^10*c.k,115443546169471+c.lower,115443935457610+c.upper)) = pointBounds67920 := by
 decide +kernel
def cuts67921 : List PrefixCut := [⟨64,181149390,181149498⟩]
theorem checked67921 : checkPrefixCuts (2^48) 8906473473 10 Manual.Count131072.C067921.packed 64 cuts67921 = true := by
 decide +kernel
def cuts67922 : List PrefixCut := [⟨37,103783607,103783672⟩,
⟨64,181273116,181273225⟩]
theorem checked67922 : checkPrefixCuts (2^48) 8906604545 10 Manual.Count131072.C067922.packed 64 cuts67922 = true := by
 decide +kernel
def pointBounds67922 : List (Nat × Nat × Nat) := [(8906680320,115444010516328,115444399804742)]
theorem point_links_checked67922 : (cuts67922.take 1).map (fun c => (8906604545-1+2*2^10*c.k,115443906732721+c.lower,115444296021070+c.upper)) = pointBounds67922 := by
 decide +kernel
def cuts67923 : List PrefixCut := [⟨64,181744502,181744609⟩]
theorem checked67923 : checkPrefixCuts (2^48) 8906735617 10 Manual.Count131072.C067923.packed 64 cuts67923 = true := by
 decide +kernel
def cuts67924 : List PrefixCut := [⟨45,126028177,126028253⟩,
⟨64,177791621,177791727⟩]
theorem checked67924 : checkPrefixCuts (2^48) 8906866689 10 Manual.Count131072.C067924.packed 64 cuts67924 = true := by
 decide +kernel
def pointBounds67924 : List (Nat × Nat × Nat) := [(8906958848,115444395778516,115444785067157)]
theorem point_links_checked67924 : (cuts67924.take 1).map (fun c => (8906866689-1+2*2^10*c.k,115444269750339+c.lower,115444659038904+c.upper)) = pointBounds67924 := by
 decide +kernel
def cuts67925 : List PrefixCut := [⟨64,178515815,178515921⟩]
theorem checked67925 : checkPrefixCuts (2^48) 8906997761 10 Manual.Count131072.C067925.packed 64 cuts67925 = true := by
 decide +kernel
def cuts67926 : List PrefixCut := [⟨53,148650577,148650665⟩,
⟨64,180124832,180124936⟩]
theorem checked67926 : checkPrefixCuts (2^48) 8907128833 10 Manual.Count131072.C067926.packed 64 cuts67926 = true := by
 decide +kernel
def pointBounds67926 : List (Nat × Nat × Nat) := [(8907237376,115444774708352,115445163997217)]
theorem point_links_checked67926 : (cuts67926.take 1).map (fun c => (8907128833-1+2*2^10*c.k,115444626057775+c.lower,115445015346552+c.upper)) = pointBounds67926 := by
 decide +kernel
def cuts67927 : List PrefixCut := [⟨64,181891803,181891906⟩]
theorem checked67927 : checkPrefixCuts (2^48) 8907259905 10 Manual.Count131072.C067927.packed 64 cuts67927 = true := by
 decide +kernel
def cuts67928 : List PrefixCut := [⟨61,174526396,174526498⟩,
⟨64,183311111,183311219⟩]
theorem checked67928 : checkPrefixCuts (2^48) 8907390977 10 Manual.Count131072.C067928.packed 64 cuts67928 = true := by
 decide +kernel
def pointBounds67928 : List (Nat × Nat × Nat) := [(8907515904,115445162600806,115445551889892)]
theorem point_links_checked67928 : (cuts67928.take 1).map (fun c => (8907390977-1+2*2^10*c.k,115444988074410+c.lower,115445377363394+c.upper)) = pointBounds67928 := by
 decide +kernel
def cuts67929 : List PrefixCut := [⟨64,182486840,182486944⟩]
theorem checked67929 : checkPrefixCuts (2^48) 8907522049 10 Manual.Count131072.C067929.packed 64 cuts67929 = true := by
 decide +kernel
def cuts67930 : List PrefixCut := [⟨64,181125399,181125503⟩]
theorem checked67930 : checkPrefixCuts (2^48) 8907653121 10 Manual.Count131072.C067930.packed 64 cuts67930 = true := by
 decide +kernel
def cuts67931 : List PrefixCut := [⟨5,14314227,14314237⟩,
⟨64,181565112,181565217⟩]
theorem checked67931 : checkPrefixCuts (2^48) 8907784193 10 Manual.Count131072.C067931.packed 64 cuts67931 = true := by
 decide +kernel
def pointBounds67931 : List (Nat × Nat × Nat) := [(8907794432,115445549311987,115445938601297)]
theorem point_links_checked67931 : (cuts67931.take 1).map (fun c => (8907784193-1+2*2^10*c.k,115445534997760+c.lower,115445924287060+c.upper)) = pointBounds67931 := by
 decide +kernel
def cuts67932 : List PrefixCut := [⟨64,179129395,179129500⟩]
theorem checked67932 : checkPrefixCuts (2^48) 8907915265 10 Manual.Count131072.C067932.packed 64 cuts67932 = true := by
 decide +kernel
def cuts67933 : List PrefixCut := [⟨13,37127388,37127410⟩,
⟨64,182602483,182602593⟩]
theorem checked67933 : checkPrefixCuts (2^48) 8908046337 10 Manual.Count131072.C067933.packed 64 cuts67933 = true := by
 decide +kernel
def pointBounds67933 : List (Nat × Nat × Nat) := [(8908072960,115445932819655,115446322109187)]
theorem point_links_checked67933 : (cuts67933.take 1).map (fun c => (8908046337-1+2*2^10*c.k,115445895692267+c.lower,115446284981777+c.upper)) = pointBounds67933 := by
 decide +kernel
def cuts67934 : List PrefixCut := [⟨64,182062647,182062751⟩]
theorem checked67934 : checkPrefixCuts (2^48) 8908177409 10 Manual.Count131072.C067934.packed 64 cuts67934 = true := by
 decide +kernel
def cuts67935 : List PrefixCut := [⟨21,59907572,59907607⟩,
⟨64,180006187,180006296⟩]
theorem checked67935 : checkPrefixCuts (2^48) 8908308481 10 Manual.Count131072.C067935.packed 64 cuts67935 = true := by
 decide +kernel
def pointBounds67935 : List (Nat × Nat × Nat) := [(8908351488,115446320264969,115446709554728)]
theorem point_links_checked67935 : (cuts67935.take 1).map (fun c => (8908308481-1+2*2^10*c.k,115446260357397+c.lower,115446649647121+c.upper)) = pointBounds67935 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000247
