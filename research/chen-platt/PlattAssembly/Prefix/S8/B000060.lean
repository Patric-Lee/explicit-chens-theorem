import PlattAssemblyKernel
import PlattCertificates.Count131072.C071920
import PlattCertificates.Count131072.C071921
import PlattCertificates.Count131072.C071922
import PlattCertificates.Count131072.C071923
import PlattCertificates.Count131072.C071924
import PlattCertificates.Count131072.C071925
import PlattCertificates.Count131072.C071926
import PlattCertificates.Count131072.C071927
import PlattCertificates.Count131072.C071928
import PlattCertificates.Count131072.C071929
import PlattCertificates.Count131072.C071930
import PlattCertificates.Count131072.C071931
import PlattCertificates.Count131072.C071932
import PlattCertificates.Count131072.C071933
import PlattCertificates.Count131072.C071934
import PlattCertificates.Count131072.C071935
import PlattCertificates.Count131072.C071936
import PlattCertificates.Count131072.C071937
import PlattCertificates.Count131072.C071938
import PlattCertificates.Count131072.C071939
import PlattCertificates.Count131072.C071940
import PlattCertificates.Count131072.C071941
import PlattCertificates.Count131072.C071942
import PlattCertificates.Count131072.C071943
import PlattCertificates.Count131072.C071944
import PlattCertificates.Count131072.C071945
import PlattCertificates.Count131072.C071946
import PlattCertificates.Count131072.C071947
import PlattCertificates.Count131072.C071948
import PlattCertificates.Count131072.C071949
import PlattCertificates.Count131072.C071950
import PlattCertificates.Count131072.C071951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71920 : List PrefixCut := [⟨46,122132826,122132895⟩,
⟨64,168066624,168066722⟩]
theorem checked71920 : checkPrefixCuts (2^48) 9430630401 10 Manual.Count131072.C071920.packed 64 cuts71920 = true := by
 decide +kernel
def pointBounds71920 : List (Nat × Nat × Nat) := [(9430724608,116145560071582,116145949772796)]
theorem point_links_checked71920 : (cuts71920.take 1).map (fun c => (9430630401-1+2*2^10*c.k,116145437938756+c.lower,116145827639901+c.upper)) = pointBounds71920 := by
 decide +kernel
def cuts71921 : List PrefixCut := [⟨64,170810140,170810247⟩]
theorem checked71921 : checkPrefixCuts (2^48) 9430761473 10 Manual.Count131072.C071921.packed 64 cuts71921 = true := by
 decide +kernel
def cuts71922 : List PrefixCut := [⟨62,164868462,164868555⟩,
⟨64,170360061,170360156⟩]
theorem checked71922 : checkPrefixCuts (2^48) 9430892545 10 Manual.Count131072.C071922.packed 64 cuts71922 = true := by
 decide +kernel
def pointBounds71922 : List (Nat × Nat × Nat) := [(9431019520,116145941683982,116146331385425)]
theorem point_links_checked71922 : (cuts71922.take 1).map (fun c => (9430892545-1+2*2^10*c.k,116145776815520+c.lower,116146166516870+c.upper)) = pointBounds71922 := by
 decide +kernel
def cuts71923 : List PrefixCut := [⟨64,170805374,170805480⟩]
theorem checked71923 : checkPrefixCuts (2^48) 9431023617 10 Manual.Count131072.C071923.packed 64 cuts71923 = true := by
 decide +kernel
def cuts71924 : List PrefixCut := [⟨64,168296022,168296122⟩]
theorem checked71924 : checkPrefixCuts (2^48) 9431154689 10 Manual.Count131072.C071924.packed 64 cuts71924 = true := by
 decide +kernel
def cuts71925 : List PrefixCut := [⟨14,37067192,37067212⟩,
⟨64,172650995,172651097⟩]
theorem checked71925 : checkPrefixCuts (2^48) 9431285761 10 Manual.Count131072.C071925.packed 64 cuts71925 = true := by
 decide +kernel
def pointBounds71925 : List (Nat × Nat × Nat) := [(9431314432,116146323344169,116146713045840)]
theorem point_links_checked71925 : (cuts71925.take 1).map (fun c => (9431285761-1+2*2^10*c.k,116146286276977+c.lower,116146675978628+c.upper)) = pointBounds71925 := by
 decide +kernel
def cuts71926 : List PrefixCut := [⟨64,170798260,170798363⟩]
theorem checked71926 : checkPrefixCuts (2^48) 9431416833 10 Manual.Count131072.C071926.packed 64 cuts71926 = true := by
 decide +kernel
def cuts71927 : List PrefixCut := [⟨30,80578474,80578521⟩,
⟨64,172168712,172168810⟩]
theorem checked71927 : checkPrefixCuts (2^48) 9431547905 10 Manual.Count131072.C071927.packed 64 cuts71927 = true := by
 decide +kernel
def pointBounds71927 : List (Nat × Nat × Nat) := [(9431609344,116146710304706,116147100006609)]
theorem point_links_checked71927 : (cuts71927.take 1).map (fun c => (9431547905-1+2*2^10*c.k,116146629726232+c.lower,116147019428088+c.upper)) = pointBounds71927 := by
 decide +kernel
def cuts71928 : List PrefixCut := [⟨64,167510754,167510854⟩]
theorem checked71928 : checkPrefixCuts (2^48) 9431678977 10 Manual.Count131072.C071928.packed 64 cuts71928 = true := by
 decide +kernel
def cuts71929 : List PrefixCut := [⟨46,123191891,123191961⟩,
⟨64,172522024,172522122⟩]
theorem checked71929 : checkPrefixCuts (2^48) 9431810049 10 Manual.Count131072.C071929.packed 64 cuts71929 = true := by
 decide +kernel
def pointBounds71929 : List (Nat × Nat × Nat) := [(9431904256,116147092597589,116147482299713)]
theorem point_links_checked71929 : (cuts71929.take 1).map (fun c => (9431810049-1+2*2^10*c.k,116146969405698+c.lower,116147359107752+c.upper)) = pointBounds71929 := by
 decide +kernel
def cuts71930 : List PrefixCut := [⟨64,168341674,168341775⟩]
theorem checked71930 : checkPrefixCuts (2^48) 9431941121 10 Manual.Count131072.C071930.packed 64 cuts71930 = true := by
 decide +kernel
def cuts71931 : List PrefixCut := [⟨62,162460494,162460586⟩,
⟨64,167115832,167115927⟩]
theorem checked71931 : checkPrefixCuts (2^48) 9432072193 10 Manual.Count131072.C071931.packed 64 cuts71931 = true := by
 decide +kernel
def pointBounds71931 : List (Nat × Nat × Nat) := [(9432199168,116147472729890,116147862432235)]
theorem point_links_checked71931 : (cuts71931.take 1).map (fun c => (9432072193-1+2*2^10*c.k,116147310269396+c.lower,116147699971649+c.upper)) = pointBounds71931 := by
 decide +kernel
def cuts71932 : List PrefixCut := [⟨64,170455782,170455887⟩]
theorem checked71932 : checkPrefixCuts (2^48) 9432203265 10 Manual.Count131072.C071932.packed 64 cuts71932 = true := by
 decide +kernel
def cuts71933 : List PrefixCut := [⟨64,169438802,169438902⟩]
theorem checked71933 : checkPrefixCuts (2^48) 9432334337 10 Manual.Count131072.C071933.packed 64 cuts71933 = true := by
 decide +kernel
def cuts71934 : List PrefixCut := [⟨14,37420650,37420672⟩,
⟨64,170898644,170898750⟩]
theorem checked71934 : checkPrefixCuts (2^48) 9432465409 10 Manual.Count131072.C071934.packed 64 cuts71934 = true := by
 decide +kernel
def pointBounds71934 : List (Nat × Nat × Nat) := [(9432494080,116147854700462,116148244403037)]
theorem point_links_checked71934 : (cuts71934.take 1).map (fun c => (9432465409-1+2*2^10*c.k,116147817279812+c.lower,116148206982365+c.upper)) = pointBounds71934 := by
 decide +kernel
def cuts71935 : List PrefixCut := [⟨64,169702654,169702750⟩]
theorem checked71935 : checkPrefixCuts (2^48) 9432596481 10 Manual.Count131072.C071935.packed 64 cuts71935 = true := by
 decide +kernel
def cuts71936 : List PrefixCut := [⟨30,77793261,77793307⟩,
⟨64,168954278,168954378⟩]
theorem checked71936 : checkPrefixCuts (2^48) 9432727553 10 Manual.Count131072.C071936.packed 64 cuts71936 = true := by
 decide +kernel
def pointBounds71936 : List (Nat × Nat × Nat) := [(9432788992,116148235674371,116148625377172)]
theorem point_links_checked71936 : (cuts71936.take 1).map (fun c => (9432727553-1+2*2^10*c.k,116148157881110+c.lower,116148547583865+c.upper)) = pointBounds71936 := by
 decide +kernel
def cuts71937 : List PrefixCut := [⟨64,172562536,172562635⟩]
theorem checked71937 : checkPrefixCuts (2^48) 9432858625 10 Manual.Count131072.C071937.packed 64 cuts71937 = true := by
 decide +kernel
def cuts71938 : List PrefixCut := [⟨46,122788580,122788654⟩,
⟨64,169993969,169994072⟩]
theorem checked71938 : checkPrefixCuts (2^48) 9432989697 10 Manual.Count131072.C071938.packed 64 cuts71938 = true := by
 decide +kernel
def pointBounds71938 : List (Nat × Nat × Nat) := [(9433083904,116148622186504,116149011889532)]
theorem point_links_checked71938 : (cuts71938.take 1).map (fun c => (9432989697-1+2*2^10*c.k,116148499397924+c.lower,116148889100878+c.upper)) = pointBounds71938 := by
 decide +kernel
def cuts71939 : List PrefixCut := [⟨64,171394024,171394118⟩]
theorem checked71939 : checkPrefixCuts (2^48) 9433120769 10 Manual.Count131072.C071939.packed 64 cuts71939 = true := by
 decide +kernel
def cuts71940 : List PrefixCut := [⟨62,167244143,167244249⟩,
⟨64,171749708,171749816⟩]
theorem checked71940 : checkPrefixCuts (2^48) 9433251841 10 Manual.Count131072.C071940.packed 64 cuts71940 = true := by
 decide +kernel
def pointBounds71940 : List (Nat × Nat × Nat) := [(9433378816,116149008030060,116149397733317)]
theorem point_links_checked71940 : (cuts71940.take 1).map (fun c => (9433251841-1+2*2^10*c.k,116148840785917+c.lower,116149230489068+c.upper)) = pointBounds71940 := by
 decide +kernel
def cuts71941 : List PrefixCut := [⟨64,170583645,170583742⟩]
theorem checked71941 : checkPrefixCuts (2^48) 9433382913 10 Manual.Count131072.C071941.packed 64 cuts71941 = true := by
 decide +kernel
def cuts71942 : List PrefixCut := [⟨64,169626477,169626579⟩]
theorem checked71942 : checkPrefixCuts (2^48) 9433513985 10 Manual.Count131072.C071942.packed 64 cuts71942 = true := by
 decide +kernel
def cuts71943 : List PrefixCut := [⟨14,36878900,36878920⟩,
⟨64,168162091,168162193⟩]
theorem checked71943 : checkPrefixCuts (2^48) 9433645057 10 Manual.Count131072.C071943.packed 64 cuts71943 = true := by
 decide +kernel
def pointBounds71943 : List (Nat × Nat × Nat) := [(9433673728,116149389624647,116149779328125)]
theorem point_links_checked71943 : (cuts71943.take 1).map (fun c => (9433645057-1+2*2^10*c.k,116149352745747+c.lower,116149742449205+c.upper)) = pointBounds71943 := by
 decide +kernel
def cuts71944 : List PrefixCut := [⟨64,172694933,172695035⟩]
theorem checked71944 : checkPrefixCuts (2^48) 9433776129 10 Manual.Count131072.C071944.packed 64 cuts71944 = true := by
 decide +kernel
def cuts71945 : List PrefixCut := [⟨30,80498653,80498697⟩,
⟨64,171618431,171618529⟩]
theorem checked71945 : checkPrefixCuts (2^48) 9433907201 10 Manual.Count131072.C071945.packed 64 cuts71945 = true := by
 decide +kernel
def pointBounds71945 : List (Nat × Nat × Nat) := [(9433968640,116149774101424,116150163805130)]
theorem point_links_checked71945 : (cuts71945.take 1).map (fun c => (9433907201-1+2*2^10*c.k,116149693602771+c.lower,116150083306433+c.upper)) = pointBounds71945 := by
 decide +kernel
def cuts71946 : List PrefixCut := [⟨64,172361940,172362046⟩]
theorem checked71946 : checkPrefixCuts (2^48) 9434038273 10 Manual.Count131072.C071946.packed 64 cuts71946 = true := by
 decide +kernel
def cuts71947 : List PrefixCut := [⟨46,121221778,121221851⟩,
⟨64,170271056,170271160⟩]
theorem checked71947 : checkPrefixCuts (2^48) 9434169345 10 Manual.Count131072.C071947.packed 64 cuts71947 = true := by
 decide +kernel
def pointBounds71947 : List (Nat × Nat × Nat) := [(9434263552,116150158804920,116150548508859)]
theorem point_links_checked71947 : (cuts71947.take 1).map (fun c => (9434169345-1+2*2^10*c.k,116150037583142+c.lower,116150427287008+c.upper)) = pointBounds71947 := by
 decide +kernel
def cuts71948 : List PrefixCut := [⟨64,170268694,170268794⟩]
theorem checked71948 : checkPrefixCuts (2^48) 9434300417 10 Manual.Count131072.C071948.packed 64 cuts71948 = true := by
 decide +kernel
def cuts71949 : List PrefixCut := [⟨62,163076208,163076311⟩,
⟨64,168148064,168148170⟩]
theorem checked71949 : checkPrefixCuts (2^48) 9434431489 10 Manual.Count131072.C071949.packed 64 cuts71949 = true := by
 decide +kernel
def pointBounds71949 : List (Nat × Nat × Nat) := [(9434558464,116150541199100,116150930903273)]
theorem point_links_checked71949 : (cuts71949.take 1).map (fun c => (9434431489-1+2*2^10*c.k,116150378122892+c.lower,116150767826962+c.upper)) = pointBounds71949 := by
 decide +kernel
def cuts71950 : List PrefixCut := [⟨64,171278333,171278433⟩]
theorem checked71950 : checkPrefixCuts (2^48) 9434562561 10 Manual.Count131072.C071950.packed 64 cuts71950 = true := by
 decide +kernel
def cuts71951 : List PrefixCut := [⟨64,168650578,168650675⟩]
theorem checked71951 : checkPrefixCuts (2^48) 9434693633 10 Manual.Count131072.C071951.packed 64 cuts71951 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000060
