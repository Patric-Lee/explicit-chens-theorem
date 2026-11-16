import PlattAssemblyKernel
import PlattCertificates.Count131072.C058928
import PlattCertificates.Count131072.C058929
import PlattCertificates.Count131072.C058930
import PlattCertificates.Count131072.C058931
import PlattCertificates.Count131072.C058932
import PlattCertificates.Count131072.C058933
import PlattCertificates.Count131072.C058934
import PlattCertificates.Count131072.C058935
import PlattCertificates.Count131072.C058936
import PlattCertificates.Count131072.C058937
import PlattCertificates.Count131072.C058938
import PlattCertificates.Count131072.C058939
import PlattCertificates.Count131072.C058940
import PlattCertificates.Count131072.C058941
import PlattCertificates.Count131072.C058942
import PlattCertificates.Count131072.C058943
import PlattCertificates.Count131072.C058944
import PlattCertificates.Count131072.C058945
import PlattCertificates.Count131072.C058946
import PlattCertificates.Count131072.C058947
import PlattCertificates.Count131072.C058948
import PlattCertificates.Count131072.C058949
import PlattCertificates.Count131072.C058950
import PlattCertificates.Count131072.C058951
import PlattCertificates.Count131072.C058952
import PlattCertificates.Count131072.C058953
import PlattCertificates.Count131072.C058954
import PlattCertificates.Count131072.C058955
import PlattCertificates.Count131072.C058956
import PlattCertificates.Count131072.C058957
import PlattCertificates.Count131072.C058958
import PlattCertificates.Count131072.C058959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000279
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58928 : List PrefixCut := [⟨64,208707442,208707564⟩]
theorem checked58928 : checkPrefixCuts (2^48) 7727742977 10 Manual.Count131072.C058928.packed 64 cuts58928 = true := by
 decide +kernel
def cuts58929 : List PrefixCut := [⟨18,60389733,60389768⟩,
⟨64,209432374,209432496⟩]
theorem checked58929 : checkPrefixCuts (2^48) 7727874049 10 Manual.Count131072.C058929.packed 64 cuts58929 = true := by
 decide +kernel
def pointBounds58929 : List (Nat × Nat × Nat) := [(7727910912,113694362092989,113694750373263)]
theorem point_links_checked58929 : (cuts58929.take 1).map (fun c => (7727874049-1+2*2^10*c.k,113694301703256+c.lower,113694689983495+c.upper)) = pointBounds58929 := by
 decide +kernel
def cuts58930 : List PrefixCut := [⟨64,207389149,207389269⟩]
theorem checked58930 : checkPrefixCuts (2^48) 7728005121 10 Manual.Count131072.C058930.packed 64 cuts58930 = true := by
 decide +kernel
def cuts58931 : List PrefixCut := [⟨8,27098009,27098024⟩,
⟨64,213285975,213286093⟩]
theorem checked58931 : checkPrefixCuts (2^48) 7728136193 10 Manual.Count131072.C058931.packed 64 cuts58931 = true := by
 decide +kernel
def pointBounds58931 : List (Nat × Nat × Nat) := [(7728152576,113694745622788,113695133903284)]
theorem point_links_checked58931 : (cuts58931.take 1).map (fun c => (7728136193-1+2*2^10*c.k,113694718524779+c.lower,113695106805260+c.upper)) = pointBounds58931 := by
 decide +kernel
def cuts58932 : List PrefixCut := [⟨62,206872297,206872417⟩,
⟨64,213100265,213100389⟩]
theorem checked58932 : checkPrefixCuts (2^48) 7728267265 10 Manual.Count131072.C058932.packed 64 cuts58932 = true := by
 decide +kernel
def pointBounds58932 : List (Nat × Nat × Nat) := [(7728394240,113695138683051,113695526963770)]
theorem point_links_checked58932 : (cuts58932.take 1).map (fun c => (7728267265-1+2*2^10*c.k,113694931810754+c.lower,113695320091353+c.upper)) = pointBounds58932 := by
 decide +kernel
def cuts58933 : List PrefixCut := [⟨64,209782356,209782478⟩]
theorem checked58933 : checkPrefixCuts (2^48) 7728398337 10 Manual.Count131072.C058933.packed 64 cuts58933 = true := by
 decide +kernel
def cuts58934 : List PrefixCut := [⟨52,167968982,167969078⟩,
⟨64,207156560,207156678⟩]
theorem checked58934 : checkPrefixCuts (2^48) 7728529409 10 Manual.Count131072.C058934.packed 64 cuts58934 = true := by
 decide +kernel
def pointBounds58934 : List (Nat × Nat × Nat) := [(7728635904,113695522662357,113695910943298)]
theorem point_links_checked58934 : (cuts58934.take 1).map (fun c => (7728529409-1+2*2^10*c.k,113695354693375+c.lower,113695742974220+c.upper)) = pointBounds58934 := by
 decide +kernel
def cuts58935 : List PrefixCut := [⟨64,211814717,211814836⟩]
theorem checked58935 : checkPrefixCuts (2^48) 7728660481 10 Manual.Count131072.C058935.packed 64 cuts58935 = true := by
 decide +kernel
def cuts58936 : List PrefixCut := [⟨42,139301920,139301995⟩,
⟨64,210755006,210755123⟩]
theorem checked58936 : checkPrefixCuts (2^48) 7728791553 10 Manual.Count131072.C058936.packed 64 cuts58936 = true := by
 decide +kernel
def pointBounds58936 : List (Nat × Nat × Nat) := [(7728877568,113695912966572,113696301247729)]
theorem point_links_checked58936 : (cuts58936.take 1).map (fun c => (7728791553-1+2*2^10*c.k,113695773664652+c.lower,113696161945734+c.upper)) = pointBounds58936 := by
 decide +kernel
def cuts58937 : List PrefixCut := [⟨64,208748426,208748544⟩]
theorem checked58937 : checkPrefixCuts (2^48) 7728922625 10 Manual.Count131072.C058937.packed 64 cuts58937 = true := by
 decide +kernel
def cuts58938 : List PrefixCut := [⟨32,103680947,103681007⟩,
⟨64,209363972,209364091⟩]
theorem checked58938 : checkPrefixCuts (2^48) 7729053697 10 Manual.Count131072.C058938.packed 64 cuts58938 = true := by
 decide +kernel
def pointBounds58938 : List (Nat × Nat × Nat) := [(7729119232,113696296849031,113696685130408)]
theorem point_links_checked58938 : (cuts58938.take 1).map (fun c => (7729053697-1+2*2^10*c.k,113696193168084+c.lower,113696581449401+c.upper)) = pointBounds58938 := by
 decide +kernel
def cuts58939 : List PrefixCut := [⟨64,209943091,209943210⟩]
theorem checked58939 : checkPrefixCuts (2^48) 7729184769 10 Manual.Count131072.C058939.packed 64 cuts58939 = true := by
 decide +kernel
def cuts58940 : List PrefixCut := [⟨22,71412615,71412657⟩,
⟨64,210012373,210012496⟩]
theorem checked58940 : checkPrefixCuts (2^48) 7729315841 10 Manual.Count131072.C058940.packed 64 cuts58940 = true := by
 decide +kernel
def pointBounds58940 : List (Nat × Nat × Nat) := [(7729360896,113696683887762,113697072169359)]
theorem point_links_checked58940 : (cuts58940.take 1).map (fun c => (7729315841-1+2*2^10*c.k,113696612475147+c.lower,113697000756702+c.upper)) = pointBounds58940 := by
 decide +kernel
def cuts58941 : List PrefixCut := [⟨64,212630746,212630868⟩]
theorem checked58941 : checkPrefixCuts (2^48) 7729446913 10 Manual.Count131072.C058941.packed 64 cuts58941 = true := by
 decide +kernel
def cuts58942 : List PrefixCut := [⟨12,37871848,37871871⟩,
⟨64,208767137,208767257⟩]
theorem checked58942 : checkPrefixCuts (2^48) 7729577985 10 Manual.Count131072.C058942.packed 64 cuts58942 = true := by
 decide +kernel
def pointBounds58942 : List (Nat × Nat × Nat) := [(7729602560,113697072990114,113697461271937)]
theorem point_links_checked58942 : (cuts58942.take 1).map (fun c => (7729577985-1+2*2^10*c.k,113697035118266+c.lower,113697423400066+c.upper)) = pointBounds58942 := by
 decide +kernel
def cuts58943 : List PrefixCut := [⟨64,206396671,206396788⟩]
theorem checked58943 : checkPrefixCuts (2^48) 7729709057 10 Manual.Count131072.C058943.packed 64 cuts58943 = true := by
 decide +kernel
def cuts58944 : List PrefixCut := [⟨2,5899077,5899081⟩,
⟨64,209051375,209051491⟩]
theorem checked58944 : checkPrefixCuts (2^48) 7729840129 10 Manual.Count131072.C058944.packed 64 cuts58944 = true := by
 decide +kernel
def pointBounds58944 : List (Nat × Nat × Nat) := [(7729844224,113697456181151,113697844463192)]
theorem point_links_checked58944 : (cuts58944.take 1).map (fun c => (7729840129-1+2*2^10*c.k,113697450282074+c.lower,113697838564111+c.upper)) = pointBounds58944 := by
 decide +kernel
def cuts58945 : List PrefixCut := [⟨56,178715864,178715967⟩,
⟨64,204277697,204277814⟩]
theorem checked58945 : checkPrefixCuts (2^48) 7729971201 10 Manual.Count131072.C058945.packed 64 cuts58945 = true := by
 decide +kernel
def pointBounds58945 : List (Nat × Nat × Nat) := [(7730085888,113697838049313,113698226331569)]
theorem point_links_checked58945 : (cuts58945.take 1).map (fun c => (7729971201-1+2*2^10*c.k,113697659333449+c.lower,113698047615602+c.upper)) = pointBounds58945 := by
 decide +kernel
def cuts58946 : List PrefixCut := [⟨64,208024726,208024845⟩]
theorem checked58946 : checkPrefixCuts (2^48) 7730102273 10 Manual.Count131072.C058946.packed 64 cuts58946 = true := by
 decide +kernel
def cuts58947 : List PrefixCut := [⟨46,151765172,151765258⟩,
⟨64,211116211,211116332⟩]
theorem checked58947 : checkPrefixCuts (2^48) 7730233345 10 Manual.Count131072.C058947.packed 64 cuts58947 = true := by
 decide +kernel
def pointBounds58947 : List (Nat × Nat × Nat) := [(7730327552,113698223401044,113698611683519)]
theorem point_links_checked58947 : (cuts58947.take 1).map (fun c => (7730233345-1+2*2^10*c.k,113698071635872+c.lower,113698459918261+c.upper)) = pointBounds58947 := by
 decide +kernel
def cuts58948 : List PrefixCut := [⟨64,209838251,209838368⟩]
theorem checked58948 : checkPrefixCuts (2^48) 7730364417 10 Manual.Count131072.C058948.packed 64 cuts58948 = true := by
 decide +kernel
def cuts58949 : List PrefixCut := [⟨36,117461253,117461319⟩,
⟨64,209506985,209507104⟩]
theorem checked58949 : checkPrefixCuts (2^48) 7730495489 10 Manual.Count131072.C058949.packed 64 cuts58949 = true := by
 decide +kernel
def pointBounds58949 : List (Nat × Nat × Nat) := [(7730569216,113698610051587,113698998334280)]
theorem point_links_checked58949 : (cuts58949.take 1).map (fun c => (7730495489-1+2*2^10*c.k,113698492590334+c.lower,113698880872961+c.upper)) = pointBounds58949 := by
 decide +kernel
def cuts58950 : List PrefixCut := [⟨64,210923435,210923553⟩]
theorem checked58950 : checkPrefixCuts (2^48) 7730626561 10 Manual.Count131072.C058950.packed 64 cuts58950 = true := by
 decide +kernel
def cuts58951 : List PrefixCut := [⟨26,86363618,86363666⟩,
⟨64,210264487,210264605⟩]
theorem checked58951 : checkPrefixCuts (2^48) 7730757633 10 Manual.Count131072.C058951.packed 64 cuts58951 = true := by
 decide +kernel
def pointBounds58951 : List (Nat × Nat × Nat) := [(7730810880,113698999384372,113699387667284)]
theorem point_links_checked58951 : (cuts58951.take 1).map (fun c => (7730757633-1+2*2^10*c.k,113698913020754+c.lower,113699301303618+c.upper)) = pointBounds58951 := by
 decide +kernel
def cuts58952 : List PrefixCut := [⟨64,209205074,209205192⟩]
theorem checked58952 : checkPrefixCuts (2^48) 7730888705 10 Manual.Count131072.C058952.packed 64 cuts58952 = true := by
 decide +kernel
def cuts58953 : List PrefixCut := [⟨16,53702435,53702465⟩,
⟨64,209128712,209128833⟩]
theorem checked58953 : checkPrefixCuts (2^48) 7731019777 10 Manual.Count131072.C058953.packed 64 cuts58953 = true := by
 decide +kernel
def pointBounds58953 : List (Nat × Nat × Nat) := [(7731052544,113699386192750,113699774475880)]
theorem point_links_checked58953 : (cuts58953.take 1).map (fun c => (7731019777-1+2*2^10*c.k,113699332490315+c.lower,113699720773415+c.upper)) = pointBounds58953 := by
 decide +kernel
def cuts58954 : List PrefixCut := [⟨64,208251381,208251501⟩]
theorem checked58954 : checkPrefixCuts (2^48) 7731150849 10 Manual.Count131072.C058954.packed 64 cuts58954 = true := by
 decide +kernel
def cuts58955 : List PrefixCut := [⟨6,18749731,18749740⟩,
⟨64,207374060,207374173⟩]
theorem checked58955 : checkPrefixCuts (2^48) 7731281921 10 Manual.Count131072.C058955.packed 64 cuts58955 = true := by
 decide +kernel
def pointBounds58955 : List (Nat × Nat × Nat) := [(7731294208,113699768620139,113700156903489)]
theorem point_links_checked58955 : (cuts58955.take 1).map (fun c => (7731281921-1+2*2^10*c.k,113699749870408+c.lower,113700138153749+c.upper)) = pointBounds58955 := by
 decide +kernel
def cuts58956 : List PrefixCut := [⟨60,197104071,197104183⟩,
⟨64,210173847,210173966⟩]
theorem checked58956 : checkPrefixCuts (2^48) 7731412993 10 Manual.Count131072.C058956.packed 64 cuts58956 = true := by
 decide +kernel
def pointBounds58956 : List (Nat × Nat × Nat) := [(7731535872,113700154348539,113700542632105)]
theorem point_links_checked58956 : (cuts58956.take 1).map (fun c => (7731412993-1+2*2^10*c.k,113699957244468+c.lower,113700345527922+c.upper)) = pointBounds58956 := by
 decide +kernel
def cuts58957 : List PrefixCut := [⟨64,208714071,208714183⟩]
theorem checked58957 : checkPrefixCuts (2^48) 7731544065 10 Manual.Count131072.C058957.packed 64 cuts58957 = true := by
 decide +kernel
def cuts58958 : List PrefixCut := [⟨50,160765268,160765362⟩,
⟨64,206271358,206271478⟩]
theorem checked58958 : checkPrefixCuts (2^48) 7731675137 10 Manual.Count131072.C058958.packed 64 cuts58958 = true := by
 decide +kernel
def pointBounds58958 : List (Nat × Nat × Nat) := [(7731777536,113700536897654,113700925181433)]
theorem point_links_checked58958 : (cuts58958.take 1).map (fun c => (7731675137-1+2*2^10*c.k,113700376132386+c.lower,113700764416071+c.upper)) = pointBounds58958 := by
 decide +kernel
def cuts58959 : List PrefixCut := [⟨64,208852579,208852701⟩]
theorem checked58959 : checkPrefixCuts (2^48) 7731806209 10 Manual.Count131072.C058959.packed 64 cuts58959 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000279
