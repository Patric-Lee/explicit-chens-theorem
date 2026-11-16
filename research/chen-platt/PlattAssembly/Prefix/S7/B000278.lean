import PlattAssemblyKernel
import PlattCertificates.Count131072.C068896
import PlattCertificates.Count131072.C068897
import PlattCertificates.Count131072.C068898
import PlattCertificates.Count131072.C068899
import PlattCertificates.Count131072.C068900
import PlattCertificates.Count131072.C068901
import PlattCertificates.Count131072.C068902
import PlattCertificates.Count131072.C068903
import PlattCertificates.Count131072.C068904
import PlattCertificates.Count131072.C068905
import PlattCertificates.Count131072.C068906
import PlattCertificates.Count131072.C068907
import PlattCertificates.Count131072.C068908
import PlattCertificates.Count131072.C068909
import PlattCertificates.Count131072.C068910
import PlattCertificates.Count131072.C068911
import PlattCertificates.Count131072.C068912
import PlattCertificates.Count131072.C068913
import PlattCertificates.Count131072.C068914
import PlattCertificates.Count131072.C068915
import PlattCertificates.Count131072.C068916
import PlattCertificates.Count131072.C068917
import PlattCertificates.Count131072.C068918
import PlattCertificates.Count131072.C068919
import PlattCertificates.Count131072.C068920
import PlattCertificates.Count131072.C068921
import PlattCertificates.Count131072.C068922
import PlattCertificates.Count131072.C068923
import PlattCertificates.Count131072.C068924
import PlattCertificates.Count131072.C068925
import PlattCertificates.Count131072.C068926
import PlattCertificates.Count131072.C068927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000278
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68896 : List PrefixCut := [⟨64,176468313,176468420⟩]
theorem checked68896 : checkPrefixCuts (2^48) 9034268673 10 Manual.Count131072.C068896.packed 64 cuts68896 = true := by
 decide +kernel
def cuts68897 : List PrefixCut := [⟨9,25360882,25360894⟩,
⟨64,179955206,179955310⟩]
theorem checked68897 : checkPrefixCuts (2^48) 9034399745 10 Manual.Count131072.C068897.packed 64 cuts68897 = true := by
 decide +kernel
def pointBounds68897 : List (Nat × Nat × Nat) := [(9034418176,115618918392870,115619307783533)]
theorem point_links_checked68897 : (cuts68897.take 1).map (fun c => (9034399745-1+2*2^10*c.k,115618893031988+c.lower,115619282422639+c.upper)) = pointBounds68897 := by
 decide +kernel
def cuts68898 : List PrefixCut := [⟨64,180949559,180949665⟩]
theorem checked68898 : checkPrefixCuts (2^48) 9034530817 10 Manual.Count131072.C068898.packed 64 cuts68898 = true := by
 decide +kernel
def cuts68899 : List PrefixCut := [⟨19,53742260,53742293⟩,
⟨64,178703790,178703897⟩]
theorem checked68899 : checkPrefixCuts (2^48) 9034661889 10 Manual.Count131072.C068899.packed 64 cuts68899 = true := by
 decide +kernel
def pointBounds68899 : List (Nat × Nat × Nat) := [(9034700800,115619307679013,115619697069907)]
theorem point_links_checked68899 : (cuts68899.take 1).map (fun c => (9034661889-1+2*2^10*c.k,115619253936753+c.lower,115619643327614+c.upper)) = pointBounds68899 := by
 decide +kernel
def cuts68900 : List PrefixCut := [⟨64,180445829,180445935⟩]
theorem checked68900 : checkPrefixCuts (2^48) 9034792961 10 Manual.Count131072.C068900.packed 64 cuts68900 = true := by
 decide +kernel
def cuts68901 : List PrefixCut := [⟨29,80439611,80439658⟩,
⟨64,178231293,178231396⟩]
theorem checked68901 : checkPrefixCuts (2^48) 9034924033 10 Manual.Count131072.C068901.packed 64 cuts68901 = true := by
 decide +kernel
def pointBounds68901 : List (Nat × Nat × Nat) := [(9034983424,115619693525983,115620082917104)]
theorem point_links_checked68901 : (cuts68901.take 1).map (fun c => (9034924033-1+2*2^10*c.k,115619613086372+c.lower,115620002477446+c.upper)) = pointBounds68901 := by
 decide +kernel
def cuts68902 : List PrefixCut := [⟨64,179599460,179599562⟩]
theorem checked68902 : checkPrefixCuts (2^48) 9035055105 10 Manual.Count131072.C068902.packed 64 cuts68902 = true := by
 decide +kernel
def cuts68903 : List PrefixCut := [⟨39,109222612,109222676⟩,
⟨64,179659157,179659264⟩]
theorem checked68903 : checkPrefixCuts (2^48) 9035186177 10 Manual.Count131072.C068903.packed 64 cuts68903 = true := by
 decide +kernel
def pointBounds68903 : List (Nat × Nat × Nat) := [(9035266048,115620080139737,115620469531080)]
theorem point_links_checked68903 : (cuts68903.take 1).map (fun c => (9035186177-1+2*2^10*c.k,115619970917125+c.lower,115620360308404+c.upper)) = pointBounds68903 := by
 decide +kernel
def cuts68904 : List PrefixCut := [⟨64,177257812,177257915⟩]
theorem checked68904 : checkPrefixCuts (2^48) 9035317249 10 Manual.Count131072.C068904.packed 64 cuts68904 = true := by
 decide +kernel
def cuts68905 : List PrefixCut := [⟨49,135480550,135480628⟩,
⟨64,177255233,177255337⟩]
theorem checked68905 : checkPrefixCuts (2^48) 9035448321 10 Manual.Count131072.C068905.packed 64 cuts68905 = true := by
 decide +kernel
def pointBounds68905 : List (Nat × Nat × Nat) := [(9035548672,115620463314644,115620852706211)]
theorem point_links_checked68905 : (cuts68905.take 1).map (fun c => (9035448321-1+2*2^10*c.k,115620327834094+c.lower,115620717225583+c.upper)) = pointBounds68905 := by
 decide +kernel
def cuts68906 : List PrefixCut := [⟨64,178747944,178748053⟩]
theorem checked68906 : checkPrefixCuts (2^48) 9035579393 10 Manual.Count131072.C068906.packed 64 cuts68906 = true := by
 decide +kernel
def cuts68907 : List PrefixCut := [⟨59,164914332,164914428⟩,
⟨64,178527297,178527401⟩]
theorem checked68907 : checkPrefixCuts (2^48) 9035710465 10 Manual.Count131072.C068907.packed 64 cuts68907 = true := by
 decide +kernel
def pointBounds68907 : List (Nat × Nat × Nat) := [(9035831296,115620848751603,115621238143401)]
theorem point_links_checked68907 : (cuts68907.take 1).map (fun c => (9035710465-1+2*2^10*c.k,115620683837271+c.lower,115621073228973+c.upper)) = pointBounds68907 := by
 decide +kernel
def cuts68908 : List PrefixCut := [⟨64,176250701,176250799⟩]
theorem checked68908 : checkPrefixCuts (2^48) 9035841537 10 Manual.Count131072.C068908.packed 64 cuts68908 = true := by
 decide +kernel
def cuts68909 : List PrefixCut := [⟨64,178054867,178054972⟩]
theorem checked68909 : checkPrefixCuts (2^48) 9035972609 10 Manual.Count131072.C068909.packed 64 cuts68909 = true := by
 decide +kernel
def cuts68910 : List PrefixCut := [⟨5,14235556,14235563⟩,
⟨64,180045863,180045969⟩]
theorem checked68910 : checkPrefixCuts (2^48) 9036103681 10 Manual.Count131072.C068910.packed 64 cuts68910 = true := by
 decide +kernel
def pointBounds68910 : List (Nat × Nat × Nat) := [(9036113920,115621230905692,115621620297708)]
theorem point_links_checked68910 : (cuts68910.take 1).map (fun c => (9036103681-1+2*2^10*c.k,115621216670136+c.lower,115621606062145+c.upper)) = pointBounds68910 := by
 decide +kernel
def cuts68911 : List PrefixCut := [⟨64,178579237,178579338⟩]
theorem checked68911 : checkPrefixCuts (2^48) 9036234753 10 Manual.Count131072.C068911.packed 64 cuts68911 = true := by
 decide +kernel
def cuts68912 : List PrefixCut := [⟨15,40992179,40992202⟩,
⟨64,177392974,177393079⟩]
theorem checked68912 : checkPrefixCuts (2^48) 9036365825 10 Manual.Count131072.C068912.packed 64 cuts68912 = true := by
 decide +kernel
def pointBounds68912 : List (Nat × Nat × Nat) := [(9036396544,115621616287415,115622005679654)]
theorem point_links_checked68912 : (cuts68912.take 1).map (fun c => (9036365825-1+2*2^10*c.k,115621575295236+c.lower,115621964687452+c.upper)) = pointBounds68912 := by
 decide +kernel
def cuts68913 : List PrefixCut := [⟨64,176082177,176082281⟩]
theorem checked68913 : checkPrefixCuts (2^48) 9036496897 10 Manual.Count131072.C068913.packed 64 cuts68913 = true := by
 decide +kernel
def cuts68914 : List PrefixCut := [⟨25,70675116,70675160⟩,
⟨64,178851803,178851908⟩]
theorem checked68914 : checkPrefixCuts (2^48) 9036627969 10 Manual.Count131072.C068914.packed 64 cuts68914 = true := by
 decide +kernel
def pointBounds68914 : List (Nat × Nat × Nat) := [(9036679168,115621999445503,115622388837972)]
theorem point_links_checked68914 : (cuts68914.take 1).map (fun c => (9036627969-1+2*2^10*c.k,115621928770387+c.lower,115622318162812+c.upper)) = pointBounds68914 := by
 decide +kernel
def cuts68915 : List PrefixCut := [⟨64,177509850,177509957⟩]
theorem checked68915 : checkPrefixCuts (2^48) 9036759041 10 Manual.Count131072.C068915.packed 64 cuts68915 = true := by
 decide +kernel
def cuts68916 : List PrefixCut := [⟨35,97397276,97397335⟩,
⟨64,177071224,177071332⟩]
theorem checked68916 : checkPrefixCuts (2^48) 9036890113 10 Manual.Count131072.C068916.packed 64 cuts68916 = true := by
 decide +kernel
def pointBounds68916 : List (Nat × Nat × Nat) := [(9036961792,115622382529316,115622771922012)]
theorem point_links_checked68916 : (cuts68916.take 1).map (fun c => (9036890113-1+2*2^10*c.k,115622285132040+c.lower,115622674524677+c.upper)) = pointBounds68916 := by
 decide +kernel
def cuts68917 : List PrefixCut := [⟨64,178345664,178345773⟩]
theorem checked68917 : checkPrefixCuts (2^48) 9037021185 10 Manual.Count131072.C068917.packed 64 cuts68917 = true := by
 decide +kernel
def cuts68918 : List PrefixCut := [⟨45,123463760,123463834⟩,
⟨64,176287428,176287535⟩]
theorem checked68918 : checkPrefixCuts (2^48) 9037152257 10 Manual.Count131072.C068918.packed 64 cuts68918 = true := by
 decide +kernel
def pointBounds68918 : List (Nat × Nat × Nat) := [(9037244416,115622764012688,115623153405616)]
theorem point_links_checked68918 : (cuts68918.take 1).map (fun c => (9037152257-1+2*2^10*c.k,115622640548928+c.lower,115623029941782+c.upper)) = pointBounds68918 := by
 decide +kernel
def cuts68919 : List PrefixCut := [⟨64,177437271,177437368⟩]
theorem checked68919 : checkPrefixCuts (2^48) 9037283329 10 Manual.Count131072.C068919.packed 64 cuts68919 = true := by
 decide +kernel
def cuts68920 : List PrefixCut := [⟨55,155539717,155539803⟩,
⟨64,180144338,180144440⟩]
theorem checked68920 : checkPrefixCuts (2^48) 9037414401 10 Manual.Count131072.C068920.packed 64 cuts68920 = true := by
 decide +kernel
def pointBounds68920 : List (Nat × Nat × Nat) := [(9037527040,115623149813344,115623539206488)]
theorem point_links_checked68920 : (cuts68920.take 1).map (fun c => (9037414401-1+2*2^10*c.k,115622994273627+c.lower,115623383666685+c.upper)) = pointBounds68920 := by
 decide +kernel
def cuts68921 : List PrefixCut := [⟨64,178304175,178304272⟩]
theorem checked68921 : checkPrefixCuts (2^48) 9037545473 10 Manual.Count131072.C068921.packed 64 cuts68921 = true := by
 decide +kernel
def cuts68922 : List PrefixCut := [⟨64,177118110,177118210⟩]
theorem checked68922 : checkPrefixCuts (2^48) 9037676545 10 Manual.Count131072.C068922.packed 64 cuts68922 = true := by
 decide +kernel
def cuts68923 : List PrefixCut := [⟨1,2927550,2927552⟩,
⟨64,177800693,177800805⟩]
theorem checked68923 : checkPrefixCuts (2^48) 9037807617 10 Manual.Count131072.C068923.packed 64 cuts68923 = true := by
 decide +kernel
def pointBounds68923 : List (Nat × Nat × Nat) := [(9037809664,115623532767800,115623922161159)]
theorem point_links_checked68923 : (cuts68923.take 1).map (fun c => (9037807617-1+2*2^10*c.k,115623529840250+c.lower,115623919233607+c.upper)) = pointBounds68923 := by
 decide +kernel
def cuts68924 : List PrefixCut := [⟨64,179791305,179791402⟩]
theorem checked68924 : checkPrefixCuts (2^48) 9037938689 10 Manual.Count131072.C068924.packed 64 cuts68924 = true := by
 decide +kernel
def cuts68925 : List PrefixCut := [⟨11,30084345,30084361⟩,
⟨64,176580961,176581064⟩]
theorem checked68925 : checkPrefixCuts (2^48) 9038069761 10 Manual.Count131072.C068925.packed 64 cuts68925 = true := by
 decide +kernel
def pointBounds68925 : List (Nat × Nat × Nat) := [(9038092288,115623917516593,115624306910175)]
theorem point_links_checked68925 : (cuts68925.take 1).map (fun c => (9038069761-1+2*2^10*c.k,115623887432248+c.lower,115624276825814+c.upper)) = pointBounds68925 := by
 decide +kernel
def cuts68926 : List PrefixCut := [⟨64,179038673,179038773⟩]
theorem checked68926 : checkPrefixCuts (2^48) 9038200833 10 Manual.Count131072.C068926.packed 64 cuts68926 = true := by
 decide +kernel
def cuts68927 : List PrefixCut := [⟨21,57644352,57644388⟩,
⟨64,177385526,177385632⟩]
theorem checked68927 : checkPrefixCuts (2^48) 9038331905 10 Manual.Count131072.C068927.packed 64 cuts68927 = true := by
 decide +kernel
def pointBounds68927 : List (Nat × Nat × Nat) := [(9038374912,115624300696234,115624690090039)]
theorem point_links_checked68927 : (cuts68927.take 1).map (fun c => (9038331905-1+2*2^10*c.k,115624243051882+c.lower,115624632445651+c.upper)) = pointBounds68927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000278
