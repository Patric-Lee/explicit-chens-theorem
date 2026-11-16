import PlattAssemblyKernel
import PlattCertificates.Count131072.C072912
import PlattCertificates.Count131072.C072913
import PlattCertificates.Count131072.C072914
import PlattCertificates.Count131072.C072915
import PlattCertificates.Count131072.C072916
import PlattCertificates.Count131072.C072917
import PlattCertificates.Count131072.C072918
import PlattCertificates.Count131072.C072919
import PlattCertificates.Count131072.C072920
import PlattCertificates.Count131072.C072921
import PlattCertificates.Count131072.C072922
import PlattCertificates.Count131072.C072923
import PlattCertificates.Count131072.C072924
import PlattCertificates.Count131072.C072925
import PlattCertificates.Count131072.C072926
import PlattCertificates.Count131072.C072927
import PlattCertificates.Count131072.C072928
import PlattCertificates.Count131072.C072929
import PlattCertificates.Count131072.C072930
import PlattCertificates.Count131072.C072931
import PlattCertificates.Count131072.C072932
import PlattCertificates.Count131072.C072933
import PlattCertificates.Count131072.C072934
import PlattCertificates.Count131072.C072935
import PlattCertificates.Count131072.C072936
import PlattCertificates.Count131072.C072937
import PlattCertificates.Count131072.C072938
import PlattCertificates.Count131072.C072939
import PlattCertificates.Count131072.C072940
import PlattCertificates.Count131072.C072941
import PlattCertificates.Count131072.C072942
import PlattCertificates.Count131072.C072943
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000091
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72912 : List PrefixCut := [⟨64,169107759,169107863⟩]
theorem checked72912 : checkPrefixCuts (2^48) 9560653825 10 Manual.Count131072.C072912.packed 64 cuts72912 = true := by
 decide +kernel
def cuts72913 : List PrefixCut := [⟨30,77222349,77222394⟩,
⟨64,167250688,167250786⟩]
theorem checked72913 : checkPrefixCuts (2^48) 9560784897 10 Manual.Count131072.C072913.packed 64 cuts72913 = true := by
 decide +kernel
def pointBounds72913 : List (Nat × Nat × Nat) := [(9560846336,116313429192314,116313818993319)]
theorem point_links_checked72913 : (cuts72913.take 1).map (fun c => (9560784897-1+2*2^10*c.k,116313351969965+c.lower,116313741770925+c.upper)) = pointBounds72913 := by
 decide +kernel
def cuts72914 : List PrefixCut := [⟨64,167248397,167248498⟩]
theorem checked72914 : checkPrefixCuts (2^48) 9560915969 10 Manual.Count131072.C072914.packed 64 cuts72914 = true := by
 decide +kernel
def cuts72915 : List PrefixCut := [⟨48,124500083,124500160⟩,
⟨64,165450295,165450394⟩]
theorem checked72915 : checkPrefixCuts (2^48) 9561047041 10 Manual.Count131072.C072915.packed 64 cuts72915 = true := by
 decide +kernel
def pointBounds72915 : List (Nat × Nat × Nat) := [(9561145344,116313810969133,116314200770369)]
theorem point_links_checked72915 : (cuts72915.take 1).map (fun c => (9561047041-1+2*2^10*c.k,116313686469050+c.lower,116314076270209+c.upper)) = pointBounds72915 := by
 decide +kernel
def cuts72916 : List PrefixCut := [⟨64,171012024,171012125⟩]
theorem checked72916 : checkPrefixCuts (2^48) 9561178113 10 Manual.Count131072.C072916.packed 64 cuts72916 = true := by
 decide +kernel
def cuts72917 : List PrefixCut := [⟨64,168890107,168890200⟩]
theorem checked72917 : checkPrefixCuts (2^48) 9561309185 10 Manual.Count131072.C072917.packed 64 cuts72917 = true := by
 decide +kernel
def cuts72918 : List PrefixCut := [⟨2,5534445,5534449⟩,
⟨64,166208897,166208999⟩]
theorem checked72918 : checkPrefixCuts (2^48) 9561440257 10 Manual.Count131072.C072918.packed 64 cuts72918 = true := by
 decide +kernel
def pointBounds72918 : List (Nat × Nat × Nat) := [(9561444352,116314197355921,116314587157377)]
theorem point_links_checked72918 : (cuts72918.take 1).map (fun c => (9561440257-1+2*2^10*c.k,116314191821476+c.lower,116314581622928+c.upper)) = pointBounds72918 := by
 decide +kernel
def cuts72919 : List PrefixCut := [⟨64,168061197,168061296⟩]
theorem checked72919 : checkPrefixCuts (2^48) 9561571329 10 Manual.Count131072.C072919.packed 64 cuts72919 = true := by
 decide +kernel
def cuts72920 : List PrefixCut := [⟨20,52664003,52664031⟩,
⟨64,168176651,168176749⟩]
theorem checked72920 : checkPrefixCuts (2^48) 9561702401 10 Manual.Count131072.C072920.packed 64 cuts72920 = true := by
 decide +kernel
def pointBounds72920 : List (Nat × Nat × Nat) := [(9561743360,116314578755573,116314968557254)]
theorem point_links_checked72920 : (cuts72920.take 1).map (fun c => (9561702401-1+2*2^10*c.k,116314526091570+c.lower,116314915893223+c.upper)) = pointBounds72920 := by
 decide +kernel
def cuts72921 : List PrefixCut := [⟨64,169204642,169204745⟩]
theorem checked72921 : checkPrefixCuts (2^48) 9561833473 10 Manual.Count131072.C072921.packed 64 cuts72921 = true := by
 decide +kernel
def cuts72922 : List PrefixCut := [⟨38,101086014,101086074⟩,
⟨64,168613596,168613699⟩]
theorem checked72922 : checkPrefixCuts (2^48) 9561964545 10 Manual.Count131072.C072922.packed 64 cuts72922 = true := by
 decide +kernel
def pointBounds72922 : List (Nat × Nat × Nat) := [(9562042368,116314964558877,116315354360791)]
theorem point_links_checked72922 : (cuts72922.take 1).map (fun c => (9561964545-1+2*2^10*c.k,116314863472863+c.lower,116315253274717+c.upper)) = pointBounds72922 := by
 decide +kernel
def cuts72923 : List PrefixCut := [⟨64,167787068,167787168⟩]
theorem checked72923 : checkPrefixCuts (2^48) 9562095617 10 Manual.Count131072.C072923.packed 64 cuts72923 = true := by
 decide +kernel
def cuts72924 : List PrefixCut := [⟨56,147739020,147739105⟩,
⟨64,168638400,168638496⟩]
theorem checked72924 : checkPrefixCuts (2^48) 9562226689 10 Manual.Count131072.C072924.packed 64 cuts72924 = true := by
 decide +kernel
def pointBounds72924 : List (Nat × Nat × Nat) := [(9562341376,116315347612547,116315737414689)]
theorem point_links_checked72924 : (cuts72924.take 1).map (fun c => (9562226689-1+2*2^10*c.k,116315199873527+c.lower,116315589675584+c.upper)) = pointBounds72924 := by
 decide +kernel
def cuts72925 : List PrefixCut := [⟨64,169077624,169077725⟩]
theorem checked72925 : checkPrefixCuts (2^48) 9562357761 10 Manual.Count131072.C072925.packed 64 cuts72925 = true := by
 decide +kernel
def cuts72926 : List PrefixCut := [⟨64,168692644,168692749⟩]
theorem checked72926 : checkPrefixCuts (2^48) 9562488833 10 Manual.Count131072.C072926.packed 64 cuts72926 = true := by
 decide +kernel
def cuts72927 : List PrefixCut := [⟨10,27080091,27080108⟩,
⟨64,170544728,170544832⟩]
theorem checked72927 : checkPrefixCuts (2^48) 9562619905 10 Manual.Count131072.C072927.packed 64 cuts72927 = true := by
 decide +kernel
def pointBounds72927 : List (Nat × Nat × Nat) := [(9562640384,116315733362286,116316123164662)]
theorem point_links_checked72927 : (cuts72927.take 1).map (fun c => (9562619905-1+2*2^10*c.k,116315706282195+c.lower,116316096084554+c.upper)) = pointBounds72927 := by
 decide +kernel
def cuts72928 : List PrefixCut := [⟨64,164567201,164567304⟩]
theorem checked72928 : checkPrefixCuts (2^48) 9562750977 10 Manual.Count131072.C072928.packed 64 cuts72928 = true := by
 decide +kernel
def cuts72929 : List PrefixCut := [⟨28,73849955,73849996⟩,
⟨64,168597412,168597511⟩]
theorem checked72929 : checkPrefixCuts (2^48) 9562882049 10 Manual.Count131072.C072929.packed 64 cuts72929 = true := by
 decide +kernel
def pointBounds72929 : List (Nat × Nat × Nat) := [(9562939392,116316115244079,116316505046686)]
theorem point_links_checked72929 : (cuts72929.take 1).map (fun c => (9562882049-1+2*2^10*c.k,116316041394124+c.lower,116316431196690+c.upper)) = pointBounds72929 := by
 decide +kernel
def cuts72930 : List PrefixCut := [⟨64,167005688,167005795⟩]
theorem checked72930 : checkPrefixCuts (2^48) 9563013121 10 Manual.Count131072.C072930.packed 64 cuts72930 = true := by
 decide +kernel
def cuts72931 : List PrefixCut := [⟨46,120322739,120322809⟩,
⟨64,167798093,167798193⟩]
theorem checked72931 : checkPrefixCuts (2^48) 9563144193 10 Manual.Count131072.C072931.packed 64 cuts72931 = true := by
 decide +kernel
def pointBounds72931 : List (Nat × Nat × Nat) := [(9563238400,116316497319963,116316887122805)]
theorem point_links_checked72931 : (cuts72931.take 1).map (fun c => (9563144193-1+2*2^10*c.k,116316376997224+c.lower,116316766799996+c.upper)) = pointBounds72931 := by
 decide +kernel
def cuts72932 : List PrefixCut := [⟨64,167913528,167913625⟩]
theorem checked72932 : checkPrefixCuts (2^48) 9563275265 10 Manual.Count131072.C072932.packed 64 cuts72932 = true := by
 decide +kernel
def cuts72933 : List PrefixCut := [⟨64,170972182,170972278⟩]
theorem checked72933 : checkPrefixCuts (2^48) 9563406337 10 Manual.Count131072.C072933.packed 64 cuts72933 = true := by
 decide +kernel
def pointBounds72933 : List (Nat × Nat × Nat) := [(9563537408,116316883681027,116317273484092)]
theorem point_links_checked72933 : (cuts72933.take 1).map (fun c => (9563406337-1+2*2^10*c.k,116316712708845+c.lower,116317102511814+c.upper)) = pointBounds72933 := by
 decide +kernel
def cuts72934 : List PrefixCut := [⟨64,170028013,170028111⟩]
theorem checked72934 : checkPrefixCuts (2^48) 9563537409 10 Manual.Count131072.C072934.packed 64 cuts72934 = true := by
 decide +kernel
def cuts72935 : List PrefixCut := [⟨64,166611631,166611731⟩]
theorem checked72935 : checkPrefixCuts (2^48) 9563668481 10 Manual.Count131072.C072935.packed 64 cuts72935 = true := by
 decide +kernel
def cuts72936 : List PrefixCut := [⟨18,47560860,47560890⟩,
⟨64,167963191,167963293⟩]
theorem checked72936 : checkPrefixCuts (2^48) 9563799553 10 Manual.Count131072.C072936.packed 64 cuts72936 = true := by
 decide +kernel
def pointBounds72936 : List (Nat × Nat × Nat) := [(9563836416,116317267881531,116317657684824)]
theorem point_links_checked72936 : (cuts72936.take 1).map (fun c => (9563799553-1+2*2^10*c.k,116317220320671+c.lower,116317610123934+c.upper)) = pointBounds72936 := by
 decide +kernel
def cuts72937 : List PrefixCut := [⟨64,168637792,168637894⟩]
theorem checked72937 : checkPrefixCuts (2^48) 9563930625 10 Manual.Count131072.C072937.packed 64 cuts72937 = true := by
 decide +kernel
def cuts72938 : List PrefixCut := [⟨36,93235392,93235450⟩,
⟨64,167840851,167840955⟩]
theorem checked72938 : checkPrefixCuts (2^48) 9564061697 10 Manual.Count131072.C072938.packed 64 cuts72938 = true := by
 decide +kernel
def pointBounds72938 : List (Nat × Nat × Nat) := [(9564135424,116317650157046,116318039960571)]
theorem point_links_checked72938 : (cuts72938.take 1).map (fun c => (9564061697-1+2*2^10*c.k,116317556921654+c.lower,116317946725121+c.upper)) = pointBounds72938 := by
 decide +kernel
def cuts72939 : List PrefixCut := [⟨64,166926233,166926332⟩]
theorem checked72939 : checkPrefixCuts (2^48) 9564192769 10 Manual.Count131072.C072939.packed 64 cuts72939 = true := by
 decide +kernel
def cuts72940 : List PrefixCut := [⟨54,141761900,141761982⟩,
⟨64,168836852,168836951⟩]
theorem checked72940 : checkPrefixCuts (2^48) 9564323841 10 Manual.Count131072.C072940.packed 64 cuts72940 = true := by
 decide +kernel
def pointBounds72940 : List (Nat × Nat × Nat) := [(9564434432,116318033450638,116318423254390)]
theorem point_links_checked72940 : (cuts72940.take 1).map (fun c => (9564323841-1+2*2^10*c.k,116317891688738+c.lower,116318281492408+c.upper)) = pointBounds72940 := by
 decide +kernel
def cuts72941 : List PrefixCut := [⟨64,166509650,166509749⟩]
theorem checked72941 : checkPrefixCuts (2^48) 9564454913 10 Manual.Count131072.C072941.packed 64 cuts72941 = true := by
 decide +kernel
def cuts72942 : List PrefixCut := [⟨64,169126521,169126621⟩]
theorem checked72942 : checkPrefixCuts (2^48) 9564585985 10 Manual.Count131072.C072942.packed 64 cuts72942 = true := by
 decide +kernel
def cuts72943 : List PrefixCut := [⟨8,21306187,21306199⟩,
⟨64,166828802,166828896⟩]
theorem checked72943 : checkPrefixCuts (2^48) 9564717057 10 Manual.Count131072.C072943.packed 64 cuts72943 = true := by
 decide +kernel
def pointBounds72943 : List (Nat × Nat × Nat) := [(9564733440,116318417467948,116318807271928)]
theorem point_links_checked72943 : (cuts72943.take 1).map (fun c => (9564717057-1+2*2^10*c.k,116318396161761+c.lower,116318785965729+c.upper)) = pointBounds72943 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000091
