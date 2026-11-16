import PlattAssemblyKernel
import PlattCertificates.Count131072.C025920
import PlattCertificates.Count131072.C025921
import PlattCertificates.Count131072.C025922
import PlattCertificates.Count131072.C025923
import PlattCertificates.Count131072.C025924
import PlattCertificates.Count131072.C025925
import PlattCertificates.Count131072.C025926
import PlattCertificates.Count131072.C025927
import PlattCertificates.Count131072.C025928
import PlattCertificates.Count131072.C025929
import PlattCertificates.Count131072.C025930
import PlattCertificates.Count131072.C025931
import PlattCertificates.Count131072.C025932
import PlattCertificates.Count131072.C025933
import PlattCertificates.Count131072.C025934
import PlattCertificates.Count131072.C025935
import PlattCertificates.Count131072.C025936
import PlattCertificates.Count131072.C025937
import PlattCertificates.Count131072.C025938
import PlattCertificates.Count131072.C025939
import PlattCertificates.Count131072.C025940
import PlattCertificates.Count131072.C025941
import PlattCertificates.Count131072.C025942
import PlattCertificates.Count131072.C025943
import PlattCertificates.Count131072.C025944
import PlattCertificates.Count131072.C025945
import PlattCertificates.Count131072.C025946
import PlattCertificates.Count131072.C025947
import PlattCertificates.Count131072.C025948
import PlattCertificates.Count131072.C025949
import PlattCertificates.Count131072.C025950
import PlattCertificates.Count131072.C025951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000185
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25920 : List PrefixCut := [⟨22,83250898,83250944⟩,
⟨126,483774465,483774734⟩,
⟨128,491304850,491305123⟩]
theorem checked25920 : checkPrefixCuts (2^48) 3401318401 9 Manual.Count131072.C025920.packed 128 cuts25920 = true := by
 decide +kernel
def pointBounds25920 : List (Nat × Nat × Nat) := [(3401340928,103361382840287,103361765116394),(3401447424,103361783363854,103362165640184)]
theorem point_links_checked25920 : (cuts25920.take 2).map (fun c => (3401318401-1+2*2^9*c.k,103361299589389+c.lower,103361681865450+c.upper)) = pointBounds25920 := by
 decide +kernel
def cuts25921 : List PrefixCut := [⟨102,387601811,387602023⟩,
⟨128,487562123,487562389⟩]
theorem checked25921 : checkPrefixCuts (2^48) 3401449473 9 Manual.Count131072.C025921.packed 128 cuts25921 = true := by
 decide +kernel
def pointBounds25921 : List (Nat × Nat × Nat) := [(3401553920,103362178496050,103362560772596)]
theorem point_links_checked25921 : (cuts25921.take 1).map (fun c => (3401449473-1+2*2^9*c.k,103361790894239+c.lower,103362173170573+c.upper)) = pointBounds25921 := by
 decide +kernel
def cuts25922 : List PrefixCut := [⟨78,300786347,300786520⟩,
⟨128,496148937,496149217⟩]
theorem checked25922 : checkPrefixCuts (2^48) 3401580545 9 Manual.Count131072.C025922.packed 128 cuts25922 = true := by
 decide +kernel
def pointBounds25922 : List (Nat × Nat × Nat) := [(3401660416,103362579242709,103362961519482)]
theorem point_links_checked25922 : (cuts25922.take 1).map (fun c => (3401580545-1+2*2^9*c.k,103362278456362+c.lower,103362660732962+c.upper)) = pointBounds25922 := by
 decide +kernel
def cuts25923 : List PrefixCut := [⟨54,211908414,211908528⟩,
⟨128,497040161,497040428⟩]
theorem checked25923 : checkPrefixCuts (2^48) 3401711617 9 Manual.Count131072.C025923.packed 128 cuts25923 = true := by
 decide +kernel
def pointBounds25923 : List (Nat × Nat × Nat) := [(3401766912,103362986513713,103363368790707)]
theorem point_links_checked25923 : (cuts25923.take 1).map (fun c => (3401711617-1+2*2^9*c.k,103362774605299+c.lower,103363156882179+c.upper)) = pointBounds25923 := by
 decide +kernel
def cuts25924 : List PrefixCut := [⟨30,116417306,116417371⟩,
⟨128,493959546,493959817⟩]
theorem checked25924 : checkPrefixCuts (2^48) 3401842689 9 Manual.Count131072.C025924.packed 128 cuts25924 = true := by
 decide +kernel
def pointBounds25924 : List (Nat × Nat × Nat) := [(3401873408,103363388062766,103363770339978)]
theorem point_links_checked25924 : (cuts25924.take 1).map (fun c => (3401842689-1+2*2^9*c.k,103363271645460+c.lower,103363653922607+c.upper)) = pointBounds25924 := by
 decide +kernel
def cuts25925 : List PrefixCut := [⟨6,24821588,24821603⟩,
⟨110,426841947,426842185⟩,
⟨128,494188845,494189120⟩]
theorem checked25925 : checkPrefixCuts (2^48) 3401973761 9 Manual.Count131072.C025925.packed 128 cuts25925 = true := by
 decide +kernel
def pointBounds25925 : List (Nat × Nat × Nat) := [(3401979904,103363790426594,103364172704027),(3402086400,103364192446953,103364574724609)]
theorem point_links_checked25925 : (cuts25925.take 2).map (fun c => (3401973761-1+2*2^9*c.k,103363765605006+c.lower,103364147882424+c.upper)) = pointBounds25925 := by
 decide +kernel
def cuts25926 : List PrefixCut := [⟨86,329779492,329779677⟩,
⟨128,489122941,489123215⟩]
theorem checked25926 : checkPrefixCuts (2^48) 3402104833 9 Manual.Count131072.C025926.packed 128 cuts25926 = true := by
 decide +kernel
def pointBounds25926 : List (Nat × Nat × Nat) := [(3402192896,103364589573343,103364971851221)]
theorem point_links_checked25926 : (cuts25926.take 1).map (fun c => (3402104833-1+2*2^9*c.k,103364259793851+c.lower,103364642071544+c.upper)) = pointBounds25926 := by
 decide +kernel
def cuts25927 : List PrefixCut := [⟨62,239673327,239673462⟩,
⟨128,493654313,493654591⟩]
theorem checked25927 : checkPrefixCuts (2^48) 3402235905 9 Manual.Count131072.C025927.packed 128 cuts25927 = true := by
 decide +kernel
def pointBounds25927 : List (Nat × Nat × Nat) := [(3402299392,103364988590119,103365370868221)]
theorem point_links_checked25927 : (cuts25927.take 1).map (fun c => (3402235905-1+2*2^9*c.k,103364748916792+c.lower,103365131194759+c.upper)) = pointBounds25927 := by
 decide +kernel
def cuts25928 : List PrefixCut := [⟨38,148415227,148415307⟩,
⟨128,497192579,497192850⟩]
theorem checked25928 : checkPrefixCuts (2^48) 3402366977 9 Manual.Count131072.C025928.packed 128 cuts25928 = true := by
 decide +kernel
def pointBounds25928 : List (Nat × Nat × Nat) := [(3402405888,103365390986332,103365773264657)]
theorem point_links_checked25928 : (cuts25928.take 1).map (fun c => (3402366977-1+2*2^9*c.k,103365242571105+c.lower,103365624849350+c.upper)) = pointBounds25928 := by
 decide +kernel
def cuts25929 : List PrefixCut := [⟨14,56915337,56915367⟩,
⟨118,461189004,461189257⟩,
⟨128,499489702,499489976⟩]
theorem checked25929 : checkPrefixCuts (2^48) 3402498049 9 Manual.Count131072.C025929.packed 128 cuts25929 = true := by
 decide +kernel
def pointBounds25929 : List (Nat × Nat × Nat) := [(3402512384,103365796679021,103366178957567),(3402618880,103366200952688,103366583231457)]
theorem point_links_checked25929 : (cuts25929.take 2).map (fun c => (3402498049-1+2*2^9*c.k,103365739763684+c.lower,103366122042200+c.upper)) = pointBounds25929 := by
 decide +kernel
def cuts25930 : List PrefixCut := [⟨94,354792965,354793167⟩,
⟨128,485159714,485159986⟩]
theorem checked25930 : checkPrefixCuts (2^48) 3402629121 9 Manual.Count131072.C025930.packed 128 cuts25930 = true := by
 decide +kernel
def pointBounds25930 : List (Nat × Nat × Nat) := [(3402725376,103366594046351,103366976325343)]
theorem point_links_checked25930 : (cuts25930.take 1).map (fun c => (3402629121-1+2*2^9*c.k,103366239253386+c.lower,103366621532176+c.upper)) = pointBounds25930 := by
 decide +kernel
def cuts25931 : List PrefixCut := [⟨70,278017547,278017703⟩,
⟨128,502511791,502512075⟩]
theorem checked25931 : checkPrefixCuts (2^48) 3402760193 9 Manual.Count131072.C025931.packed 128 cuts25931 = true := by
 decide +kernel
def pointBounds25931 : List (Nat × Nat × Nat) := [(3402831872,103367002430647,103367384709865)]
theorem point_links_checked25931 : (cuts25931.take 1).map (fun c => (3402760193-1+2*2^9*c.k,103366724413100+c.lower,103367106692162+c.upper)) = pointBounds25931 := by
 decide +kernel
def cuts25932 : List PrefixCut := [⟨46,178583464,178583561⟩,
⟨128,501168967,501169247⟩]
theorem checked25932 : checkPrefixCuts (2^48) 3402891265 9 Manual.Count131072.C025932.packed 128 cuts25932 = true := by
 decide +kernel
def pointBounds25932 : List (Nat × Nat × Nat) := [(3402938368,103367405508355,103367787787798)]
theorem point_links_checked25932 : (cuts25932.take 1).map (fun c => (3402891265-1+2*2^9*c.k,103367226924891+c.lower,103367609204237+c.upper)) = pointBounds25932 := by
 decide +kernel
def cuts25933 : List PrefixCut := [⟨22,87427572,87427619⟩,
⟨126,487833276,487833552⟩,
⟨128,495608021,495608301⟩]
theorem checked25933 : checkPrefixCuts (2^48) 3403022337 9 Manual.Count131072.C025933.packed 128 cuts25933 = true := by
 decide +kernel
def pointBounds25933 : List (Nat × Nat × Nat) := [(3403044864,103367815521430,103368197801103),(3403151360,103368215927134,103368598207036)]
theorem point_links_checked25933 : (cuts25933.take 2).map (fun c => (3403022337-1+2*2^9*c.k,103367728093858+c.lower,103368110373484+c.upper)) = pointBounds25933 := by
 decide +kernel
def cuts25934 : List PrefixCut := [⟨102,393941813,393942036⟩,
⟨128,493438527,493438807⟩]
theorem checked25934 : checkPrefixCuts (2^48) 3403153409 9 Manual.Count131072.C025934.packed 128 cuts25934 = true := by
 decide +kernel
def pointBounds25934 : List (Nat × Nat × Nat) := [(3403257856,103368617643692,103368999923821)]
theorem point_links_checked25934 : (cuts25934.take 1).map (fun c => (3403153409-1+2*2^9*c.k,103368223701879+c.lower,103368605981785+c.upper)) = pointBounds25934 := by
 decide +kernel
def cuts25935 : List PrefixCut := [⟨78,297658444,297658609⟩,
⟨128,488953429,488953703⟩]
theorem checked25935 : checkPrefixCuts (2^48) 3403284481 9 Manual.Count131072.C025935.packed 128 cuts25935 = true := by
 decide +kernel
def pointBounds25935 : List (Nat × Nat × Nat) := [(3403364352,103369014798850,103369397079201)]
theorem point_links_checked25935 : (cuts25935.take 1).map (fun c => (3403284481-1+2*2^9*c.k,103368717140406+c.lower,103369099420592+c.upper)) = pointBounds25935 := by
 decide +kernel
def cuts25936 : List PrefixCut := [⟨54,208163420,208163537⟩,
⟨128,495633453,495633734⟩]
theorem checked25936 : checkPrefixCuts (2^48) 3403415553 9 Manual.Count131072.C025936.packed 128 cuts25936 = true := by
 decide +kernel
def pointBounds25936 : List (Nat × Nat × Nat) := [(3403470848,103369414257255,103369796537832)]
theorem point_links_checked25936 : (cuts25936.take 1).map (fun c => (3403415553-1+2*2^9*c.k,103369206093835+c.lower,103369588374295+c.upper)) = pointBounds25936 := by
 decide +kernel
def cuts25937 : List PrefixCut := [⟨30,118591934,118591999⟩,
⟨128,491975653,491975930⟩]
theorem checked25937 : checkPrefixCuts (2^48) 3403546625 9 Manual.Count131072.C025937.packed 128 cuts25937 = true := by
 decide +kernel
def pointBounds25937 : List (Nat × Nat × Nat) := [(3403577344,103369820319222,103370202600028)]
theorem point_links_checked25937 : (cuts25937.take 1).map (fun c => (3403546625-1+2*2^9*c.k,103369701727288+c.lower,103370084008029+c.upper)) = pointBounds25937 := by
 decide +kernel
def cuts25938 : List PrefixCut := [⟨6,22080154,22080168⟩,
⟨110,420260608,420260855⟩,
⟨128,490798864,490799149⟩]
theorem checked25938 : checkPrefixCuts (2^48) 3403677697 9 Manual.Count131072.C025938.packed 128 cuts25938 = true := by
 decide +kernel
def pointBounds25938 : List (Nat × Nat × Nat) := [(3403683840,103370215783095,103370598064127),(3403790336,103370613963549,103370996244814)]
theorem point_links_checked25938 : (cuts25938.take 2).map (fun c => (3403677697-1+2*2^9*c.k,103370193702941+c.lower,103370575983959+c.upper)) = pointBounds25938 := by
 decide +kernel
def cuts25939 : List PrefixCut := [⟨86,329449067,329449252⟩,
⟨128,489374308,489374586⟩]
theorem checked25939 : checkPrefixCuts (2^48) 3403808769 9 Manual.Count131072.C025939.packed 128 cuts25939 = true := by
 decide +kernel
def pointBounds25939 : List (Nat × Nat × Nat) := [(3403896832,103371013950872,103371396232360)]
theorem point_links_checked25939 : (cuts25939.take 1).map (fun c => (3403808769-1+2*2^9*c.k,103370684501805+c.lower,103371066783108+c.upper)) = pointBounds25939 := by
 decide +kernel
def cuts25940 : List PrefixCut := [⟨62,244184012,244184146⟩,
⟨128,502585723,502586000⟩]
theorem checked25940 : checkPrefixCuts (2^48) 3403939841 9 Manual.Count131072.C025940.packed 128 cuts25940 = true := by
 decide +kernel
def pointBounds25940 : List (Nat × Nat × Nat) := [(3404003328,103371418060125,103371800341840)]
theorem point_links_checked25940 : (cuts25940.take 1).map (fun c => (3403939841-1+2*2^9*c.k,103371173876113+c.lower,103371556157694+c.upper)) = pointBounds25940 := by
 decide +kernel
def cuts25941 : List PrefixCut := [⟨38,143793130,143793213⟩,
⟨128,492147884,492148162⟩]
theorem checked25941 : checkPrefixCuts (2^48) 3404070913 9 Manual.Count131072.C025941.packed 128 cuts25941 = true := by
 decide +kernel
def pointBounds25941 : List (Nat × Nat × Nat) := [(3404109824,103371820254966,103372202536907)]
theorem point_links_checked25941 : (cuts25941.take 1).map (fun c => (3404070913-1+2*2^9*c.k,103371676461836+c.lower,103372058743694+c.upper)) = pointBounds25941 := by
 decide +kernel
def cuts25942 : List PrefixCut := [⟨14,53662158,53662188⟩,
⟨118,455335773,455336026⟩,
⟨128,493865344,493865619⟩]
theorem checked25942 : checkPrefixCuts (2^48) 3404201985 9 Manual.Count131072.C025942.packed 128 cuts25942 = true := by
 decide +kernel
def pointBounds25942 : List (Nat × Nat × Nat) := [(3404216320,103372222271878,103372604554044),(3404322816,103372623945493,103373006227882)]
theorem point_links_checked25942 : (cuts25942.take 2).map (fun c => (3404201985-1+2*2^9*c.k,103372168609720+c.lower,103372550891856+c.upper)) = pointBounds25942 := by
 decide +kernel
def cuts25943 : List PrefixCut := [⟨94,353623206,353623405⟩,
⟨128,486653079,486653353⟩]
theorem checked25943 : checkPrefixCuts (2^48) 3404333057 9 Manual.Count131072.C025943.packed 128 cuts25943 = true := by
 decide +kernel
def pointBounds25943 : List (Nat × Nat × Nat) := [(3404429312,103373016098270,103373398380880)]
theorem point_links_checked25943 : (cuts25943.take 1).map (fun c => (3404333057-1+2*2^9*c.k,103372662475064+c.lower,103373044757475+c.upper)) = pointBounds25943 := by
 decide +kernel
def cuts25944 : List PrefixCut := [⟨70,267709126,267709275⟩,
⟨128,488784010,488784287⟩]
theorem checked25944 : checkPrefixCuts (2^48) 3404464129 9 Manual.Count131072.C025944.packed 128 cuts25944 = true := by
 decide +kernel
def pointBounds25944 : List (Nat × Nat × Nat) := [(3404535808,103373416837269,103373799120103)]
theorem point_links_checked25944 : (cuts25944.take 1).map (fun c => (3404464129-1+2*2^9*c.k,103373149128143+c.lower,103373531410828+c.upper)) = pointBounds25944 := by
 decide +kernel
def cuts25945 : List PrefixCut := [⟨46,183785235,183785335⟩,
⟨128,499016714,499016988⟩]
theorem checked25945 : checkPrefixCuts (2^48) 3404595201 9 Manual.Count131072.C025945.packed 128 cuts25945 = true := by
 decide +kernel
def pointBounds25945 : List (Nat × Nat × Nat) := [(3404642304,103373821697388,103374203980450)]
theorem point_links_checked25945 : (cuts25945.take 1).map (fun c => (3404595201-1+2*2^9*c.k,103373637912153+c.lower,103374020195115+c.upper)) = pointBounds25945 := by
 decide +kernel
def cuts25946 : List PrefixCut := [⟨22,87135807,87135859⟩,
⟨126,485770422,485770694⟩,
⟨128,493789282,493789558⟩]
theorem checked25946 : checkPrefixCuts (2^48) 3404726273 9 Manual.Count131072.C025946.packed 128 cuts25946 = true := by
 decide +kernel
def pointBounds25946 : List (Nat × Nat × Nat) := [(3404748800,103374224064674,103374606347962),(3404855296,103374622699289,103375004982797)]
theorem point_links_checked25946 : (cuts25946.take 2).map (fun c => (3404726273-1+2*2^9*c.k,103374136928867+c.lower,103374519212103+c.upper)) = pointBounds25946 := by
 decide +kernel
def cuts25947 : List PrefixCut := [⟨102,391512591,391512807⟩,
⟨128,489306203,489306474⟩]
theorem checked25947 : checkPrefixCuts (2^48) 3404857345 9 Manual.Count131072.C025947.packed 128 cuts25947 = true := by
 decide +kernel
def pointBounds25947 : List (Nat × Nat × Nat) := [(3404961792,103375022230740,103375404514468)]
theorem point_links_checked25947 : (cuts25947.take 1).map (fun c => (3404857345-1+2*2^9*c.k,103374630718149+c.lower,103375013001661+c.upper)) = pointBounds25947 := by
 decide +kernel
def cuts25948 : List PrefixCut := [⟨78,300815994,300816158⟩,
⟨128,498628287,498628556⟩]
theorem checked25948 : checkPrefixCuts (2^48) 3404988417 9 Manual.Count131072.C025948.packed 128 cuts25948 = true := by
 decide +kernel
def pointBounds25948 : List (Nat × Nat × Nat) := [(3405068288,103375420840346,103375803124293)]
theorem point_links_checked25948 : (cuts25948.take 1).map (fun c => (3404988417-1+2*2^9*c.k,103375120024352+c.lower,103375502308135+c.upper)) = pointBounds25948 := by
 decide +kernel
def cuts25949 : List PrefixCut := [⟨54,212936263,212936381⟩,
⟨128,496873385,496873660⟩]
theorem checked25949 : checkPrefixCuts (2^48) 3405119489 9 Manual.Count131072.C025949.packed 128 cuts25949 = true := by
 decide +kernel
def pointBounds25949 : List (Nat × Nat × Nat) := [(3405174784,103375831588902,103376213873072)]
theorem point_links_checked25949 : (cuts25949.take 1).map (fun c => (3405119489-1+2*2^9*c.k,103375618652639+c.lower,103376000936691+c.upper)) = pointBounds25949 := by
 decide +kernel
def cuts25950 : List PrefixCut := [⟨30,115391560,115391627⟩,
⟨128,489993657,489993937⟩]
theorem checked25950 : checkPrefixCuts (2^48) 3405250561 9 Manual.Count131072.C025950.packed 128 cuts25950 = true := by
 decide +kernel
def pointBounds25950 : List (Nat × Nat × Nat) := [(3405281280,103376230917584,103376613201978)]
theorem point_links_checked25950 : (cuts25950.take 1).map (fun c => (3405250561-1+2*2^9*c.k,103376115526024+c.lower,103376497810351+c.upper)) = pointBounds25950 := by
 decide +kernel
def cuts25951 : List PrefixCut := [⟨6,23391600,23391612⟩,
⟨110,426745381,426745619⟩,
⟨128,492371819,492372095⟩]
theorem checked25951 : checkPrefixCuts (2^48) 3405381633 9 Manual.Count131072.C025951.packed 128 cuts25951 = true := by
 decide +kernel
def pointBounds25951 : List (Nat × Nat × Nat) := [(3405387776,103376628911281,103377011195900),(3405494272,103377032265062,103377414549907)]
theorem point_links_checked25951 : (cuts25951.take 2).map (fun c => (3405381633-1+2*2^9*c.k,103376605519681+c.lower,103376987804288+c.upper)) = pointBounds25951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000185
