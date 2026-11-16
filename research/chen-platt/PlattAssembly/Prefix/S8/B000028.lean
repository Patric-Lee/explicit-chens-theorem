import PlattAssemblyKernel
import PlattCertificates.Count131072.C070896
import PlattCertificates.Count131072.C070897
import PlattCertificates.Count131072.C070898
import PlattCertificates.Count131072.C070899
import PlattCertificates.Count131072.C070900
import PlattCertificates.Count131072.C070901
import PlattCertificates.Count131072.C070902
import PlattCertificates.Count131072.C070903
import PlattCertificates.Count131072.C070904
import PlattCertificates.Count131072.C070905
import PlattCertificates.Count131072.C070906
import PlattCertificates.Count131072.C070907
import PlattCertificates.Count131072.C070908
import PlattCertificates.Count131072.C070909
import PlattCertificates.Count131072.C070910
import PlattCertificates.Count131072.C070911
import PlattCertificates.Count131072.C070912
import PlattCertificates.Count131072.C070913
import PlattCertificates.Count131072.C070914
import PlattCertificates.Count131072.C070915
import PlattCertificates.Count131072.C070916
import PlattCertificates.Count131072.C070917
import PlattCertificates.Count131072.C070918
import PlattCertificates.Count131072.C070919
import PlattCertificates.Count131072.C070920
import PlattCertificates.Count131072.C070921
import PlattCertificates.Count131072.C070922
import PlattCertificates.Count131072.C070923
import PlattCertificates.Count131072.C070924
import PlattCertificates.Count131072.C070925
import PlattCertificates.Count131072.C070926
import PlattCertificates.Count131072.C070927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70896 : List PrefixCut := [⟨64,169826964,169827066⟩]
theorem checked70896 : checkPrefixCuts (2^48) 9296412673 10 Manual.Count131072.C070896.packed 64 cuts70896 = true := by
 decide +kernel
def cuts70897 : List PrefixCut := [⟨1,3118569,3118571⟩,
⟨64,174971704,174971807⟩]
theorem checked70897 : checkPrefixCuts (2^48) 9296543745 10 Manual.Count131072.C070897.packed 64 cuts70897 = true := by
 decide +kernel
def pointBounds70897 : List (Nat × Nat × Nat) := [(9296545792,115969901257502,115970290854710)]
theorem point_links_checked70897 : (cuts70897.take 1).map (fun c => (9296543745-1+2*2^10*c.k,115969898138933+c.lower,115970287736139+c.upper)) = pointBounds70897 := by
 decide +kernel
def cuts70898 : List PrefixCut := [⟨64,171487390,171487489⟩]
theorem checked70898 : checkPrefixCuts (2^48) 9296674817 10 Manual.Count131072.C070898.packed 64 cuts70898 = true := by
 decide +kernel
def cuts70899 : List PrefixCut := [⟨15,40812676,40812700⟩,
⟨64,170758350,170758452⟩]
theorem checked70899 : checkPrefixCuts (2^48) 9296805889 10 Manual.Count131072.C070899.packed 64 cuts70899 = true := by
 decide +kernel
def pointBounds70899 : List (Nat × Nat × Nat) := [(9296836608,115970285410703,115970675008135)]
theorem point_links_checked70899 : (cuts70899.take 1).map (fun c => (9296805889-1+2*2^10*c.k,115970244598027+c.lower,115970634195435+c.upper)) = pointBounds70899 := by
 decide +kernel
def cuts70900 : List PrefixCut := [⟨64,175388148,175388251⟩]
theorem checked70900 : checkPrefixCuts (2^48) 9296936961 10 Manual.Count131072.C070900.packed 64 cuts70900 = true := by
 decide +kernel
def cuts70901 : List PrefixCut := [⟨29,77777924,77777969⟩,
⟨64,172721428,172721524⟩]
theorem checked70901 : checkPrefixCuts (2^48) 9297068033 10 Manual.Count131072.C070901.packed 64 cuts70901 = true := by
 decide +kernel
def pointBounds70901 : List (Nat × Nat × Nat) := [(9297127424,115970668522449,115971058120107)]
theorem point_links_checked70901 : (cuts70901.take 1).map (fun c => (9297068033-1+2*2^10*c.k,115970590744525+c.lower,115970980342138+c.upper)) = pointBounds70901 := by
 decide +kernel
def cuts70902 : List PrefixCut := [⟨64,175837335,175837439⟩]
theorem checked70902 : checkPrefixCuts (2^48) 9297199105 10 Manual.Count131072.C070902.packed 64 cuts70902 = true := by
 decide +kernel
def cuts70903 : List PrefixCut := [⟨43,116194164,116194234⟩,
⟨64,173049586,173049688⟩]
theorem checked70903 : checkPrefixCuts (2^48) 9297330177 10 Manual.Count131072.C070903.packed 64 cuts70903 = true := by
 decide +kernel
def pointBounds70903 : List (Nat × Nat × Nat) := [(9297418240,115971055497452,115971445095335)]
theorem point_links_checked70903 : (cuts70903.take 1).map (fun c => (9297330177-1+2*2^10*c.k,115970939303288+c.lower,115971328901101+c.upper)) = pointBounds70903 := by
 decide +kernel
def cuts70904 : List PrefixCut := [⟨64,170958225,170958327⟩]
theorem checked70904 : checkPrefixCuts (2^48) 9297461249 10 Manual.Count131072.C070904.packed 64 cuts70904 = true := by
 decide +kernel
def cuts70905 : List PrefixCut := [⟨57,152307318,152307402⟩,
⟨64,170986099,170986195⟩]
theorem checked70905 : checkPrefixCuts (2^48) 9297592321 10 Manual.Count131072.C070905.packed 64 cuts70905 = true := by
 decide +kernel
def pointBounds70905 : List (Nat × Nat × Nat) := [(9297709056,115971435618417,115971825216518)]
theorem point_links_checked70905 : (cuts70905.take 1).map (fun c => (9297592321-1+2*2^10*c.k,115971283311099+c.lower,115971672909116+c.upper)) = pointBounds70905 := by
 decide +kernel
def cuts70906 : List PrefixCut := [⟨64,170499312,170499412⟩]
theorem checked70906 : checkPrefixCuts (2^48) 9297723393 10 Manual.Count131072.C070906.packed 64 cuts70906 = true := by
 decide +kernel
def cuts70907 : List PrefixCut := [⟨64,169437352,169437454⟩]
theorem checked70907 : checkPrefixCuts (2^48) 9297854465 10 Manual.Count131072.C070907.packed 64 cuts70907 = true := by
 decide +kernel
def cuts70908 : List PrefixCut := [⟨7,18254409,18254420⟩,
⟨64,172159473,172159579⟩]
theorem checked70908 : checkPrefixCuts (2^48) 9297985537 10 Manual.Count131072.C070908.packed 64 cuts70908 = true := by
 decide +kernel
def pointBounds70908 : List (Nat × Nat × Nat) := [(9297999872,115971812488271,115972202086597)]
theorem point_links_checked70908 : (cuts70908.take 1).map (fun c => (9297985537-1+2*2^10*c.k,115971794233862+c.lower,115972183832177+c.upper)) = pointBounds70908 := by
 decide +kernel
def cuts70909 : List PrefixCut := [⟨64,176364881,176364976⟩]
theorem checked70909 : checkPrefixCuts (2^48) 9298116609 10 Manual.Count131072.C070909.packed 64 cuts70909 = true := by
 decide +kernel
def cuts70910 : List PrefixCut := [⟨21,55942196,55942234⟩,
⟨64,173153594,173153700⟩]
theorem checked70910 : checkPrefixCuts (2^48) 9298247681 10 Manual.Count131072.C070910.packed 64 cuts70910 = true := by
 decide +kernel
def pointBounds70910 : List (Nat × Nat × Nat) := [(9298290688,115972198700412,115972588298966)]
theorem point_links_checked70910 : (cuts70910.take 1).map (fun c => (9298247681-1+2*2^10*c.k,115972142758216+c.lower,115972532356732+c.upper)) = pointBounds70910 := by
 decide +kernel
def cuts70911 : List PrefixCut := [⟨64,172091662,172091762⟩]
theorem checked70911 : checkPrefixCuts (2^48) 9298378753 10 Manual.Count131072.C070911.packed 64 cuts70911 = true := by
 decide +kernel
def cuts70912 : List PrefixCut := [⟨35,95383453,95383509⟩,
⟨64,173996302,173996398⟩]
theorem checked70912 : checkPrefixCuts (2^48) 9298509825 10 Manual.Count131072.C070912.packed 64 cuts70912 = true := by
 decide +kernel
def pointBounds70912 : List (Nat × Nat × Nat) := [(9298581504,115972583386925,115972972985703)]
theorem point_links_checked70912 : (cuts70912.take 1).map (fun c => (9298509825-1+2*2^10*c.k,115972488003472+c.lower,115972877602194+c.upper)) = pointBounds70912 := by
 decide +kernel
def cuts70913 : List PrefixCut := [⟨64,170694376,170694477⟩]
theorem checked70913 : checkPrefixCuts (2^48) 9298640897 10 Manual.Count131072.C070913.packed 64 cuts70913 = true := by
 decide +kernel
def cuts70914 : List PrefixCut := [⟨49,135094799,135094874⟩,
⟨64,174717886,174717985⟩]
theorem checked70914 : checkPrefixCuts (2^48) 9298771969 10 Manual.Count131072.C070914.packed 64 cuts70914 = true := by
 decide +kernel
def pointBounds70914 : List (Nat × Nat × Nat) := [(9298872320,115972967788949,115973357387943)]
theorem point_links_checked70914 : (cuts70914.take 1).map (fun c => (9298771969-1+2*2^10*c.k,115972832694150+c.lower,115973222293069+c.upper)) = pointBounds70914 := by
 decide +kernel
def cuts70915 : List PrefixCut := [⟨64,174231100,174231202⟩]
theorem checked70915 : checkPrefixCuts (2^48) 9298903041 10 Manual.Count131072.C070915.packed 64 cuts70915 = true := by
 decide +kernel
def cuts70916 : List PrefixCut := [⟨63,169900180,169900281⟩,
⟨64,172715182,172715285⟩]
theorem checked70916 : checkPrefixCuts (2^48) 9299034113 10 Manual.Count131072.C070916.packed 64 cuts70916 = true := by
 decide +kernel
def pointBounds70916 : List (Nat × Nat × Nat) := [(9299163136,115973351543316,115973741142537)]
theorem point_links_checked70916 : (cuts70916.take 1).map (fun c => (9299034113-1+2*2^10*c.k,115973181643136+c.lower,115973571242256+c.upper)) = pointBounds70916 := by
 decide +kernel
def cuts70917 : List PrefixCut := [⟨64,172591682,172591789⟩]
theorem checked70917 : checkPrefixCuts (2^48) 9299165185 10 Manual.Count131072.C070917.packed 64 cuts70917 = true := by
 decide +kernel
def cuts70918 : List PrefixCut := [⟨64,171923348,171923445⟩]
theorem checked70918 : checkPrefixCuts (2^48) 9299296257 10 Manual.Count131072.C070918.packed 64 cuts70918 = true := by
 decide +kernel
def cuts70919 : List PrefixCut := [⟨13,34777862,34777883⟩,
⟨64,173071101,173071202⟩]
theorem checked70919 : checkPrefixCuts (2^48) 9299427329 10 Manual.Count131072.C070919.packed 64 cuts70919 = true := by
 decide +kernel
def pointBounds70919 : List (Nat × Nat × Nat) := [(9299453952,115973733651210,115974123250658)]
theorem point_links_checked70919 : (cuts70919.take 1).map (fun c => (9299427329-1+2*2^10*c.k,115973698873348+c.lower,115974088472775+c.upper)) = pointBounds70919 := by
 decide +kernel
def cuts70920 : List PrefixCut := [⟨64,173189718,173189825⟩]
theorem checked70920 : checkPrefixCuts (2^48) 9299558401 10 Manual.Count131072.C070920.packed 64 cuts70920 = true := by
 decide +kernel
def cuts70921 : List PrefixCut := [⟨27,71944745,71944792⟩,
⟨64,170493525,170493630⟩]
theorem checked70921 : checkPrefixCuts (2^48) 9299689473 10 Manual.Count131072.C070921.packed 64 cuts70921 = true := by
 decide +kernel
def pointBounds70921 : List (Nat × Nat × Nat) := [(9299744768,115974117078912,115974506678594)]
theorem point_links_checked70921 : (cuts70921.take 1).map (fun c => (9299689473-1+2*2^10*c.k,115974045134167+c.lower,115974434733802+c.upper)) = pointBounds70921 := by
 decide +kernel
def cuts70922 : List PrefixCut := [⟨64,173548049,173548139⟩]
theorem checked70922 : checkPrefixCuts (2^48) 9299820545 10 Manual.Count131072.C070922.packed 64 cuts70922 = true := by
 decide +kernel
def cuts70923 : List PrefixCut := [⟨41,111803119,111803184⟩,
⟨64,173454807,173454909⟩]
theorem checked70923 : checkPrefixCuts (2^48) 9299951617 10 Manual.Count131072.C070923.packed 64 cuts70923 = true := by
 decide +kernel
def pointBounds70923 : List (Nat × Nat × Nat) := [(9300035584,115974500978860,115974890578755)]
theorem point_links_checked70923 : (cuts70923.take 1).map (fun c => (9299951617-1+2*2^10*c.k,115974389175741+c.lower,115974778775571+c.upper)) = pointBounds70923 := by
 decide +kernel
def cuts70924 : List PrefixCut := [⟨64,170092855,170092964⟩]
theorem checked70924 : checkPrefixCuts (2^48) 9300082689 10 Manual.Count131072.C070924.packed 64 cuts70924 = true := by
 decide +kernel
def cuts70925 : List PrefixCut := [⟨55,148814176,148814259⟩,
⟨64,174115737,174115836⟩]
theorem checked70925 : checkPrefixCuts (2^48) 9300213761 10 Manual.Count131072.C070925.packed 64 cuts70925 = true := by
 decide +kernel
def pointBounds70925 : List (Nat × Nat × Nat) := [(9300326400,115974881537579,115975271137703)]
theorem point_links_checked70925 : (cuts70925.take 1).map (fun c => (9300213761-1+2*2^10*c.k,115974732723403+c.lower,115975122323444+c.upper)) = pointBounds70925 := by
 decide +kernel
def cuts70926 : List PrefixCut := [⟨64,170330190,170330293⟩]
theorem checked70926 : checkPrefixCuts (2^48) 9300344833 10 Manual.Count131072.C070926.packed 64 cuts70926 = true := by
 decide +kernel
def cuts70927 : List PrefixCut := [⟨64,174867438,174867542⟩]
theorem checked70927 : checkPrefixCuts (2^48) 9300475905 10 Manual.Count131072.C070927.packed 64 cuts70927 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000028
