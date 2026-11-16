import PlattAssemblyKernel
import PlattCertificates.Count131072.C071728
import PlattCertificates.Count131072.C071729
import PlattCertificates.Count131072.C071730
import PlattCertificates.Count131072.C071731
import PlattCertificates.Count131072.C071732
import PlattCertificates.Count131072.C071733
import PlattCertificates.Count131072.C071734
import PlattCertificates.Count131072.C071735
import PlattCertificates.Count131072.C071736
import PlattCertificates.Count131072.C071737
import PlattCertificates.Count131072.C071738
import PlattCertificates.Count131072.C071739
import PlattCertificates.Count131072.C071740
import PlattCertificates.Count131072.C071741
import PlattCertificates.Count131072.C071742
import PlattCertificates.Count131072.C071743
import PlattCertificates.Count131072.C071744
import PlattCertificates.Count131072.C071745
import PlattCertificates.Count131072.C071746
import PlattCertificates.Count131072.C071747
import PlattCertificates.Count131072.C071748
import PlattCertificates.Count131072.C071749
import PlattCertificates.Count131072.C071750
import PlattCertificates.Count131072.C071751
import PlattCertificates.Count131072.C071752
import PlattCertificates.Count131072.C071753
import PlattCertificates.Count131072.C071754
import PlattCertificates.Count131072.C071755
import PlattCertificates.Count131072.C071756
import PlattCertificates.Count131072.C071757
import PlattCertificates.Count131072.C071758
import PlattCertificates.Count131072.C071759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71728 : List PrefixCut := [⟨64,171269542,171269639⟩]
theorem checked71728 : checkPrefixCuts (2^48) 9405464577 10 Manual.Count131072.C071728.packed 64 cuts71728 = true := by
 decide +kernel
def cuts71729 : List PrefixCut := [⟨30,79364348,79364395⟩,
⟨64,170937962,170938063⟩]
theorem checked71729 : checkPrefixCuts (2^48) 9405595649 10 Manual.Count131072.C071729.packed 64 cuts71729 = true := by
 decide +kernel
def pointBounds71729 : List (Nat × Nat × Nat) := [(9405657088,116112935468212,116113325150101)]
theorem point_links_checked71729 : (cuts71729.take 1).map (fun c => (9405595649-1+2*2^10*c.k,116112856103864+c.lower,116113245785706+c.upper)) = pointBounds71729 := by
 decide +kernel
def cuts71730 : List PrefixCut := [⟨64,167583896,167583998⟩]
theorem checked71730 : checkPrefixCuts (2^48) 9405726721 10 Manual.Count131072.C071730.packed 64 cuts71730 = true := by
 decide +kernel
def cuts71731 : List PrefixCut := [⟨46,122394637,122394709⟩,
⟨64,170604023,170604123⟩]
theorem checked71731 : checkPrefixCuts (2^48) 9405857793 10 Manual.Count131072.C071731.packed 64 cuts71731 = true := by
 decide +kernel
def pointBounds71731 : List (Nat × Nat × Nat) := [(9405952000,116113317020359,116113706702476)]
theorem point_links_checked71731 : (cuts71731.take 1).map (fun c => (9405857793-1+2*2^10*c.k,116113194625722+c.lower,116113584307767+c.upper)) = pointBounds71731 := by
 decide +kernel
def cuts71732 : List PrefixCut := [⟨64,174162713,174162811⟩]
theorem checked71732 : checkPrefixCuts (2^48) 9405988865 10 Manual.Count131072.C071732.packed 64 cuts71732 = true := by
 decide +kernel
def cuts71733 : List PrefixCut := [⟨62,163477287,163477388⟩,
⟨64,169132970,169133073⟩]
theorem checked71733 : checkPrefixCuts (2^48) 9406119937 10 Manual.Count131072.C071733.packed 64 cuts71733 = true := by
 decide +kernel
def pointBounds71733 : List (Nat × Nat × Nat) := [(9406246912,116113702869745,116114092552089)]
theorem point_links_checked71733 : (cuts71733.take 1).map (fun c => (9406119937-1+2*2^10*c.k,116113539392458+c.lower,116113929074701+c.upper)) = pointBounds71733 := by
 decide +kernel
def cuts71734 : List PrefixCut := [⟨64,171344987,171345090⟩]
theorem checked71734 : checkPrefixCuts (2^48) 9406251009 10 Manual.Count131072.C071734.packed 64 cuts71734 = true := by
 decide +kernel
def cuts71735 : List PrefixCut := [⟨64,172090703,172090806⟩]
theorem checked71735 : checkPrefixCuts (2^48) 9406382081 10 Manual.Count131072.C071735.packed 64 cuts71735 = true := by
 decide +kernel
def cuts71736 : List PrefixCut := [⟨14,37912895,37912918⟩,
⟨64,170472446,170472547⟩]
theorem checked71736 : checkPrefixCuts (2^48) 9406513153 10 Manual.Count131072.C071736.packed 64 cuts71736 = true := by
 decide +kernel
def pointBounds71736 : List (Nat × Nat × Nat) := [(9406541824,116114089874013,116114479556588)]
theorem point_links_checked71736 : (cuts71736.take 1).map (fun c => (9406513153-1+2*2^10*c.k,116114051961118+c.lower,116114441643670+c.upper)) = pointBounds71736 := by
 decide +kernel
def cuts71737 : List PrefixCut := [⟨64,170380299,170380404⟩]
theorem checked71737 : checkPrefixCuts (2^48) 9406644225 10 Manual.Count131072.C071737.packed 64 cuts71737 = true := by
 decide +kernel
def cuts71738 : List PrefixCut := [⟨30,81209591,81209636⟩,
⟨64,171694515,171694614⟩]
theorem checked71738 : checkPrefixCuts (2^48) 9406775297 10 Manual.Count131072.C071738.packed 64 cuts71738 = true := by
 decide +kernel
def pointBounds71738 : List (Nat × Nat × Nat) := [(9406836736,116114474023454,116114863706257)]
theorem point_links_checked71738 : (cuts71738.take 1).map (fun c => (9406775297-1+2*2^10*c.k,116114392813863+c.lower,116114782496621+c.upper)) = pointBounds71738 := by
 decide +kernel
def cuts71739 : List PrefixCut := [⟨64,172290555,172290656⟩]
theorem checked71739 : checkPrefixCuts (2^48) 9406906369 10 Manual.Count131072.C071739.packed 64 cuts71739 = true := by
 decide +kernel
def cuts71740 : List PrefixCut := [⟨46,123875365,123875436⟩,
⟨64,171599965,171600062⟩]
theorem checked71740 : checkPrefixCuts (2^48) 9407037441 10 Manual.Count131072.C071740.packed 64 cuts71740 = true := by
 decide +kernel
def pointBounds71740 : List (Nat × Nat × Nat) := [(9407131648,116114860674298,116115250357327)]
theorem point_links_checked71740 : (cuts71740.take 1).map (fun c => (9407037441-1+2*2^10*c.k,116114736798933+c.lower,116115126481891+c.upper)) = pointBounds71740 := by
 decide +kernel
def cuts71741 : List PrefixCut := [⟨64,170789712,170789811⟩]
theorem checked71741 : checkPrefixCuts (2^48) 9407168513 10 Manual.Count131072.C071741.packed 64 cuts71741 = true := by
 decide +kernel
def cuts71742 : List PrefixCut := [⟨62,167256721,167256818⟩,
⟨64,172432966,172433067⟩]
theorem checked71742 : checkPrefixCuts (2^48) 9407299585 10 Manual.Count131072.C071742.packed 64 cuts71742 = true := by
 decide +kernel
def pointBounds71742 : List (Nat × Nat × Nat) := [(9407426560,116115246445331,116115636128582)]
theorem point_links_checked71742 : (cuts71742.take 1).map (fun c => (9407299585-1+2*2^10*c.k,116115079188610+c.lower,116115468871764+c.upper)) = pointBounds71742 := by
 decide +kernel
def cuts71743 : List PrefixCut := [⟨64,168570835,168570942⟩]
theorem checked71743 : checkPrefixCuts (2^48) 9407430657 10 Manual.Count131072.C071743.packed 64 cuts71743 = true := by
 decide +kernel
def cuts71744 : List PrefixCut := [⟨64,170812483,170812585⟩]
theorem checked71744 : checkPrefixCuts (2^48) 9407561729 10 Manual.Count131072.C071744.packed 64 cuts71744 = true := by
 decide +kernel
def cuts71745 : List PrefixCut := [⟨14,37010554,37010576⟩,
⟨64,169942441,169942538⟩]
theorem checked71745 : checkPrefixCuts (2^48) 9407692801 10 Manual.Count131072.C071745.packed 64 cuts71745 = true := by
 decide +kernel
def pointBounds71745 : List (Nat × Nat × Nat) := [(9407721472,116115628015448,116116017698934)]
theorem point_links_checked71745 : (cuts71745.take 1).map (fun c => (9407692801-1+2*2^10*c.k,116115591004894+c.lower,116115980688358+c.upper)) = pointBounds71745 := by
 decide +kernel
def cuts71746 : List PrefixCut := [⟨64,168294516,168294616⟩]
theorem checked71746 : checkPrefixCuts (2^48) 9407823873 10 Manual.Count131072.C071746.packed 64 cuts71746 = true := by
 decide +kernel
def cuts71747 : List PrefixCut := [⟨30,80271931,80271978⟩,
⟨64,172480790,172480893⟩]
theorem checked71747 : checkPrefixCuts (2^48) 9407954945 10 Manual.Count131072.C071747.packed 64 cuts71747 = true := by
 decide +kernel
def pointBounds71747 : List (Nat × Nat × Nat) := [(9408016384,116116009513782,116116399197490)]
theorem point_links_checked71747 : (cuts71747.take 1).map (fun c => (9407954945-1+2*2^10*c.k,116115929241851+c.lower,116116318925512+c.upper)) = pointBounds71747 := by
 decide +kernel
def cuts71748 : List PrefixCut := [⟨64,171730420,171730526⟩]
theorem checked71748 : checkPrefixCuts (2^48) 9408086017 10 Manual.Count131072.C071748.packed 64 cuts71748 = true := by
 decide +kernel
def cuts71749 : List PrefixCut := [⟨46,124458184,124458260⟩,
⟨64,171877623,171877725⟩]
theorem checked71749 : checkPrefixCuts (2^48) 9408217089 10 Manual.Count131072.C071749.packed 64 cuts71749 = true := by
 decide +kernel
def pointBounds71749 : List (Nat × Nat × Nat) := [(9408311296,116116397911245,116116787595191)]
theorem point_links_checked71749 : (cuts71749.take 1).map (fun c => (9408217089-1+2*2^10*c.k,116116273453061+c.lower,116116663136931+c.upper)) = pointBounds71749 := by
 decide +kernel
def cuts71750 : List PrefixCut := [⟨64,167118354,167118456⟩]
theorem checked71750 : checkPrefixCuts (2^48) 9408348161 10 Manual.Count131072.C071750.packed 64 cuts71750 = true := by
 decide +kernel
def cuts71751 : List PrefixCut := [⟨62,168671767,168671860⟩,
⟨64,174296115,174296210⟩]
theorem checked71751 : checkPrefixCuts (2^48) 9408479233 10 Manual.Count131072.C071751.packed 64 cuts71751 = true := by
 decide +kernel
def pointBounds71751 : List (Nat × Nat × Nat) := [(9408606208,116116781120805,116117170804972)]
theorem point_links_checked71751 : (cuts71751.take 1).map (fun c => (9408479233-1+2*2^10*c.k,116116612449038+c.lower,116117002133112+c.upper)) = pointBounds71751 := by
 decide +kernel
def cuts71752 : List PrefixCut := [⟨64,170135288,170135383⟩]
theorem checked71752 : checkPrefixCuts (2^48) 9408610305 10 Manual.Count131072.C071752.packed 64 cuts71752 = true := by
 decide +kernel
def cuts71753 : List PrefixCut := [⟨64,169534590,169534688⟩]
theorem checked71753 : checkPrefixCuts (2^48) 9408741377 10 Manual.Count131072.C071753.packed 64 cuts71753 = true := by
 decide +kernel
def cuts71754 : List PrefixCut := [⟨14,37903390,37903409⟩,
⟨64,170100617,170100717⟩]
theorem checked71754 : checkPrefixCuts (2^48) 9408872449 10 Manual.Count131072.C071754.packed 64 cuts71754 = true := by
 decide +kernel
def pointBounds71754 : List (Nat × Nat × Nat) := [(9408901120,116117164318421,116117554002802)]
theorem point_links_checked71754 : (cuts71754.take 1).map (fun c => (9408872449-1+2*2^10*c.k,116117126415031+c.lower,116117516099393+c.upper)) = pointBounds71754 := by
 decide +kernel
def cuts71755 : List PrefixCut := [⟨64,170158093,170158195⟩]
theorem checked71755 : checkPrefixCuts (2^48) 9409003521 10 Manual.Count131072.C071755.packed 64 cuts71755 = true := by
 decide +kernel
def cuts71756 : List PrefixCut := [⟨30,80740504,80740549⟩,
⟨64,172518991,172519092⟩]
theorem checked71756 : checkPrefixCuts (2^48) 9409134593 10 Manual.Count131072.C071756.packed 64 cuts71756 = true := by
 decide +kernel
def pointBounds71756 : List (Nat × Nat × Nat) := [(9409196032,116117547414245,116117937098854)]
theorem point_links_checked71756 : (cuts71756.take 1).map (fun c => (9409134593-1+2*2^10*c.k,116117466673741+c.lower,116117856358305+c.upper)) = pointBounds71756 := by
 decide +kernel
def cuts71757 : List PrefixCut := [⟨64,170572149,170572259⟩]
theorem checked71757 : checkPrefixCuts (2^48) 9409265665 10 Manual.Count131072.C071757.packed 64 cuts71757 = true := by
 decide +kernel
def cuts71758 : List PrefixCut := [⟨46,121451184,121451254⟩,
⟨64,169911662,169911761⟩]
theorem checked71758 : checkPrefixCuts (2^48) 9409396737 10 Manual.Count131072.C071758.packed 64 cuts71758 = true := by
 decide +kernel
def pointBounds71758 : List (Nat × Nat × Nat) := [(9409490944,116117931216065,116118320900910)]
theorem point_links_checked71758 : (cuts71758.take 1).map (fun c => (9409396737-1+2*2^10*c.k,116117809764881+c.lower,116118199449656+c.upper)) = pointBounds71758 := by
 decide +kernel
def cuts71759 : List PrefixCut := [⟨64,170268252,170268354⟩]
theorem checked71759 : checkPrefixCuts (2^48) 9409527809 10 Manual.Count131072.C071759.packed 64 cuts71759 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000054
