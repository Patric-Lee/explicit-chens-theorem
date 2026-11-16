import PlattAssemblyKernel
import PlattCertificates.Count131072.C036912
import PlattCertificates.Count131072.C036913
import PlattCertificates.Count131072.C036914
import PlattCertificates.Count131072.C036915
import PlattCertificates.Count131072.C036916
import PlattCertificates.Count131072.C036917
import PlattCertificates.Count131072.C036918
import PlattCertificates.Count131072.C036919
import PlattCertificates.Count131072.C036920
import PlattCertificates.Count131072.C036921
import PlattCertificates.Count131072.C036922
import PlattCertificates.Count131072.C036923
import PlattCertificates.Count131072.C036924
import PlattCertificates.Count131072.C036925
import PlattCertificates.Count131072.C036926
import PlattCertificates.Count131072.C036927
import PlattCertificates.Count131072.C036928
import PlattCertificates.Count131072.C036929
import PlattCertificates.Count131072.C036930
import PlattCertificates.Count131072.C036931
import PlattCertificates.Count131072.C036932
import PlattCertificates.Count131072.C036933
import PlattCertificates.Count131072.C036934
import PlattCertificates.Count131072.C036935
import PlattCertificates.Count131072.C036936
import PlattCertificates.Count131072.C036937
import PlattCertificates.Count131072.C036938
import PlattCertificates.Count131072.C036939
import PlattCertificates.Count131072.C036940
import PlattCertificates.Count131072.C036941
import PlattCertificates.Count131072.C036942
import PlattCertificates.Count131072.C036943
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000216
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36912 : List PrefixCut := [⟨64,337447069,337447274⟩]
theorem checked36912 : checkPrefixCuts (2^48) 4842061825 10 Manual.Count131072.C036912.packed 64 cuts36912 = true := by
 decide +kernel
def cuts36913 : List PrefixCut := [⟨3,16334416,16334426⟩,
⟨64,342088221,342088432⟩]
theorem checked36913 : checkPrefixCuts (2^48) 4842192897 10 Manual.Count131072.C036913.packed 64 cuts36913 = true := by
 decide +kernel
def pointBounds36913 : List (Nat × Nat × Nat) := [(4842199040,107855127165157,107855512062137)]
theorem point_links_checked36913 : (cuts36913.take 1).map (fun c => (4842192897-1+2*2^10*c.k,107855110830741+c.lower,107855495727711+c.upper)) = pointBounds36913 := by
 decide +kernel
def cuts36914 : List PrefixCut := [⟨13,69985989,69986031⟩,
⟨64,345508511,345508719⟩]
theorem checked36914 : checkPrefixCuts (2^48) 4842323969 10 Manual.Count131072.C036914.packed 64 cuts36914 = true := by
 decide +kernel
def pointBounds36914 : List (Nat × Nat × Nat) := [(4842350592,107855522904951,107855907802174)]
theorem point_links_checked36914 : (cuts36914.take 1).map (fun c => (4842323969-1+2*2^10*c.k,107855452918962+c.lower,107855837816143+c.upper)) = pointBounds36914 := by
 decide +kernel
def cuts36915 : List PrefixCut := [⟨23,126657003,126657079⟩,
⟨64,345789822,345790033⟩]
theorem checked36915 : checkPrefixCuts (2^48) 4842455041 10 Manual.Count131072.C036915.packed 64 cuts36915 = true := by
 decide +kernel
def pointBounds36915 : List (Nat × Nat × Nat) := [(4842502144,107855925084476,107856309981941)]
theorem point_links_checked36915 : (cuts36915.take 1).map (fun c => (4842455041-1+2*2^10*c.k,107855798427473+c.lower,107856183324862+c.upper)) = pointBounds36915 := by
 decide +kernel
def cuts36916 : List PrefixCut := [⟨33,176059125,176059231⟩,
⟨64,341014232,341014438⟩]
theorem checked36916 : checkPrefixCuts (2^48) 4842586113 10 Manual.Count131072.C036916.packed 64 cuts36916 = true := by
 decide +kernel
def pointBounds36916 : List (Nat × Nat × Nat) := [(4842653696,107856320276420,107856705174126)]
theorem point_links_checked36916 : (cuts36916.take 1).map (fun c => (4842586113-1+2*2^10*c.k,107856144217295+c.lower,107856529114895+c.upper)) = pointBounds36916 := by
 decide +kernel
def cuts36917 : List PrefixCut := [⟨43,229701325,229701464⟩,
⟨64,344143594,344143804⟩]
theorem checked36917 : checkPrefixCuts (2^48) 4842717185 10 Manual.Count131072.C036917.packed 64 cuts36917 = true := by
 decide +kernel
def pointBounds36917 : List (Nat × Nat × Nat) := [(4842805248,107856714932852,107857099830797)]
theorem point_links_checked36917 : (cuts36917.take 1).map (fun c => (4842717185-1+2*2^10*c.k,107856485231527+c.lower,107856870129333+c.upper)) = pointBounds36917 := by
 decide +kernel
def cuts36918 : List PrefixCut := [⟨53,284096026,284096201⟩,
⟨64,340240265,340240475⟩]
theorem checked36918 : checkPrefixCuts (2^48) 4842848257 10 Manual.Count131072.C036918.packed 64 cuts36918 = true := by
 decide +kernel
def pointBounds36918 : List (Nat × Nat × Nat) := [(4842956800,107857113471147,107857498369338)]
theorem point_links_checked36918 : (cuts36918.take 1).map (fun c => (4842848257-1+2*2^10*c.k,107856829375121+c.lower,107857214273137+c.upper)) = pointBounds36918 := by
 decide +kernel
def cuts36919 : List PrefixCut := [⟨63,333896074,333896281⟩,
⟨64,339068632,339068842⟩]
theorem checked36919 : checkPrefixCuts (2^48) 4842979329 10 Manual.Count131072.C036919.packed 64 cuts36919 = true := by
 decide +kernel
def pointBounds36919 : List (Nat × Nat × Nat) := [(4843108352,107857503511460,107857888409893)]
theorem point_links_checked36919 : (cuts36919.take 1).map (fun c => (4842979329-1+2*2^10*c.k,107857169615386+c.lower,107857554513612+c.upper)) = pointBounds36919 := by
 decide +kernel
def cuts36920 : List PrefixCut := [⟨64,341790932,341791140⟩]
theorem checked36920 : checkPrefixCuts (2^48) 4843110401 10 Manual.Count131072.C036920.packed 64 cuts36920 = true := by
 decide +kernel
def cuts36921 : List PrefixCut := [⟨9,47597771,47597801⟩,
⟨64,345094334,345094541⟩]
theorem checked36921 : checkPrefixCuts (2^48) 4843241473 10 Manual.Count131072.C036921.packed 64 cuts36921 = true := by
 decide +kernel
def pointBounds36921 : List (Nat × Nat × Nat) := [(4843259904,107857898072721,107858282971395)]
theorem point_links_checked36921 : (cuts36921.take 1).map (fun c => (4843241473-1+2*2^10*c.k,107857850474950+c.lower,107858235373594+c.upper)) = pointBounds36921 := by
 decide +kernel
def cuts36922 : List PrefixCut := [⟨19,100248785,100248847⟩,
⟨64,341539987,341540196⟩]
theorem checked36922 : checkPrefixCuts (2^48) 4843372545 10 Manual.Count131072.C036922.packed 64 cuts36922 = true := by
 decide +kernel
def pointBounds36922 : List (Nat × Nat × Nat) := [(4843411456,107858295818069,107858680716982)]
theorem point_links_checked36922 : (cuts36922.take 1).map (fun c => (4843372545-1+2*2^10*c.k,107858195569284+c.lower,107858580468135+c.upper)) = pointBounds36922 := by
 decide +kernel
def cuts36923 : List PrefixCut := [⟨29,154930712,154930808⟩,
⟨64,339206273,339206482⟩]
theorem checked36923 : checkPrefixCuts (2^48) 4843503617 10 Manual.Count131072.C036923.packed 64 cuts36923 = true := by
 decide +kernel
def pointBounds36923 : List (Nat × Nat × Nat) := [(4843563008,107858692039983,107859076939139)]
theorem point_links_checked36923 : (cuts36923.take 1).map (fun c => (4843503617-1+2*2^10*c.k,107858537109271+c.lower,107858922008331+c.upper)) = pointBounds36923 := by
 decide +kernel
def cuts36924 : List PrefixCut := [⟨39,206645735,206645861⟩,
⟨64,341986410,341986617⟩]
theorem checked36924 : checkPrefixCuts (2^48) 4843634689 10 Manual.Count131072.C036924.packed 64 cuts36924 = true := by
 decide +kernel
def pointBounds36924 : List (Nat × Nat × Nat) := [(4843714560,107859082961279,107859467860674)]
theorem point_links_checked36924 : (cuts36924.take 1).map (fun c => (4843634689-1+2*2^10*c.k,107858876315544+c.lower,107859261214813+c.upper)) = pointBounds36924 := by
 decide +kernel
def cuts36925 : List PrefixCut := [⟨49,264401208,264401366⟩,
⟨64,345231339,345231546⟩]
theorem checked36925 : checkPrefixCuts (2^48) 4843765761 10 Manual.Count131072.C036925.packed 64 cuts36925 = true := by
 decide +kernel
def pointBounds36925 : List (Nat × Nat × Nat) := [(4843866112,107859482703162,107859867602796)]
theorem point_links_checked36925 : (cuts36925.take 1).map (fun c => (4843765761-1+2*2^10*c.k,107859218301954+c.lower,107859603201430+c.upper)) = pointBounds36925 := by
 decide +kernel
def cuts36926 : List PrefixCut := [⟨59,317388369,317388568⟩,
⟨64,344757083,344757299⟩]
theorem checked36926 : checkPrefixCuts (2^48) 4843896833 10 Manual.Count131072.C036926.packed 64 cuts36926 = true := by
 decide +kernel
def pointBounds36926 : List (Nat × Nat × Nat) := [(4844017664,107859880921662,107860265821544)]
theorem point_links_checked36926 : (cuts36926.take 1).map (fun c => (4843896833-1+2*2^10*c.k,107859563533293+c.lower,107859948432976+c.upper)) = pointBounds36926 := by
 decide +kernel
def cuts36927 : List PrefixCut := [⟨64,342249216,342249424⟩]
theorem checked36927 : checkPrefixCuts (2^48) 4844027905 10 Manual.Count131072.C036927.packed 64 cuts36927 = true := by
 decide +kernel
def cuts36928 : List PrefixCut := [⟨5,25450418,25450434⟩,
⟨64,341658894,341659100⟩]
theorem checked36928 : checkPrefixCuts (2^48) 4844158977 10 Manual.Count131072.C036928.packed 64 cuts36928 = true := by
 decide +kernel
def pointBounds36928 : List (Nat × Nat × Nat) := [(4844169216,107860275990010,107860660890133)]
theorem point_links_checked36928 : (cuts36928.take 1).map (fun c => (4844158977-1+2*2^10*c.k,107860250539592+c.lower,107860635439699+c.upper)) = pointBounds36928 := by
 decide +kernel
def cuts36929 : List PrefixCut := [⟨15,77569216,77569265⟩,
⟨64,341068561,341068771⟩]
theorem checked36929 : checkPrefixCuts (2^48) 4844290049 10 Manual.Count131072.C036929.packed 64 cuts36929 = true := by
 decide +kernel
def pointBounds36929 : List (Nat × Nat × Nat) := [(4844320768,107860669767702,107861054668064)]
theorem point_links_checked36929 : (cuts36929.take 1).map (fun c => (4844290049-1+2*2^10*c.k,107860592198486+c.lower,107860977098799+c.upper)) = pointBounds36929 := by
 decide +kernel
def cuts36930 : List PrefixCut := [⟨25,134158875,134158954⟩,
⟨64,341349878,341350079⟩]
theorem checked36930 : checkPrefixCuts (2^48) 4844421121 10 Manual.Count131072.C036930.packed 64 cuts36930 = true := by
 decide +kernel
def pointBounds36930 : List (Nat × Nat × Nat) := [(4844472320,107861067425922,107861452326524)]
theorem point_links_checked36930 : (cuts36930.take 1).map (fun c => (4844421121-1+2*2^10*c.k,107860933267047+c.lower,107861318167570+c.upper)) = pointBounds36930 := by
 decide +kernel
def cuts36931 : List PrefixCut := [⟨35,185690446,185690560⟩,
⟨64,342154024,342154228⟩]
theorem checked36931 : checkPrefixCuts (2^48) 4844552193 10 Manual.Count131072.C036931.packed 64 cuts36931 = true := by
 decide +kernel
def pointBounds36931 : List (Nat × Nat × Nat) := [(4844623872,107861460307371,107861845208209)]
theorem point_links_checked36931 : (cuts36931.take 1).map (fun c => (4844552193-1+2*2^10*c.k,107861274616925+c.lower,107861659517649+c.upper)) = pointBounds36931 := by
 decide +kernel
def cuts36932 : List PrefixCut := [⟨45,235882743,235882894⟩,
⟨64,337671158,337671372⟩]
theorem checked36932 : checkPrefixCuts (2^48) 4844683265 10 Manual.Count131072.C036932.packed 64 cuts36932 = true := by
 decide +kernel
def pointBounds36932 : List (Nat × Nat × Nat) := [(4844775424,107861852653692,107862237554771)]
theorem point_links_checked36932 : (cuts36932.take 1).map (fun c => (4844683265-1+2*2^10*c.k,107861616770949+c.lower,107862001671877+c.upper)) = pointBounds36932 := by
 decide +kernel
def cuts36933 : List PrefixCut := [⟨55,297691591,297691771⟩,
⟨64,344633741,344633950⟩]
theorem checked36933 : checkPrefixCuts (2^48) 4844814337 10 Manual.Count131072.C036933.packed 64 cuts36933 = true := by
 decide +kernel
def pointBounds36933 : List (Nat × Nat × Nat) := [(4844926976,107862252133698,107862637035020)]
theorem point_links_checked36933 : (cuts36933.take 1).map (fun c => (4844814337-1+2*2^10*c.k,107861954442107+c.lower,107862339343249+c.upper)) = pointBounds36933 := by
 decide +kernel
def cuts36934 : List PrefixCut := [⟨64,340848209,340848415⟩]
theorem checked36934 : checkPrefixCuts (2^48) 4844945409 10 Manual.Count131072.C036934.packed 64 cuts36934 = true := by
 decide +kernel
def cuts36935 : List PrefixCut := [⟨1,4821887,4821890⟩,
⟨64,344731294,344731502⟩]
theorem checked36935 : checkPrefixCuts (2^48) 4845076481 10 Manual.Count131072.C036935.packed 64 cuts36935 = true := by
 decide +kernel
def pointBounds36935 : List (Nat × Nat × Nat) := [(4845078528,107862644745944,107863029647504)]
theorem point_links_checked36935 : (cuts36935.take 1).map (fun c => (4845076481-1+2*2^10*c.k,107862639924057+c.lower,107863024825614+c.upper)) = pointBounds36935 := by
 decide +kernel
def cuts36936 : List PrefixCut := [⟨11,57454303,57454340⟩,
⟨64,341294459,341294669⟩]
theorem checked36936 : checkPrefixCuts (2^48) 4845207553 10 Manual.Count131072.C036936.packed 64 cuts36936 = true := by
 decide +kernel
def pointBounds36936 : List (Nat × Nat × Nat) := [(4845230080,107863042109654,107863427011456)]
theorem point_links_checked36936 : (cuts36936.take 1).map (fun c => (4845207553-1+2*2^10*c.k,107862984655351+c.lower,107863369557116+c.upper)) = pointBounds36936 := by
 decide +kernel
def cuts36937 : List PrefixCut := [⟨21,111245476,111245544⟩,
⟨64,339019700,339019908⟩]
theorem checked36937 : checkPrefixCuts (2^48) 4845338625 10 Manual.Count131072.C036937.packed 64 cuts36937 = true := by
 decide +kernel
def pointBounds36937 : List (Nat × Nat × Nat) := [(4845381632,107863437195286,107863822097329)]
theorem point_links_checked36937 : (cuts36937.take 1).map (fun c => (4845338625-1+2*2^10*c.k,107863325949810+c.lower,107863710851785+c.upper)) = pointBounds36937 := by
 decide +kernel
def cuts36938 : List PrefixCut := [⟨31,163813610,163813709⟩,
⟨64,340985529,340985732⟩]
theorem checked36938 : checkPrefixCuts (2^48) 4845469697 10 Manual.Count131072.C036938.packed 64 cuts36938 = true := by
 decide +kernel
def pointBounds36938 : List (Nat × Nat × Nat) := [(4845533184,107863828783120,107864213685402)]
theorem point_links_checked36938 : (cuts36938.take 1).map (fun c => (4845469697-1+2*2^10*c.k,107863664969510+c.lower,107864049871693+c.upper)) = pointBounds36938 := by
 decide +kernel
def cuts36939 : List PrefixCut := [⟨41,221722844,221722983⟩,
⟨64,343067551,343067766⟩]
theorem checked36939 : checkPrefixCuts (2^48) 4845600769 10 Manual.Count131072.C036939.packed 64 cuts36939 = true := by
 decide +kernel
def pointBounds36939 : List (Nat × Nat × Nat) := [(4845684736,107864227677883,107864612580408)]
theorem point_links_checked36939 : (cuts36939.take 1).map (fun c => (4845600769-1+2*2^10*c.k,107864005955039+c.lower,107864390857425+c.upper)) = pointBounds36939 := by
 decide +kernel
def cuts36940 : List PrefixCut := [⟨51,273878076,273878244⟩,
⟨64,343987595,343987806⟩]
theorem checked36940 : checkPrefixCuts (2^48) 4845731841 10 Manual.Count131072.C036940.packed 64 cuts36940 = true := by
 decide +kernel
def pointBounds36940 : List (Nat × Nat × Nat) := [(4845836288,107864622900666,107865007803435)]
theorem point_links_checked36940 : (cuts36940.take 1).map (fun c => (4845731841-1+2*2^10*c.k,107864349022590+c.lower,107864733925191+c.upper)) = pointBounds36940 := by
 decide +kernel
def cuts36941 : List PrefixCut := [⟨61,323939237,323939432⟩,
⟨64,340551282,340551487⟩]
theorem checked36941 : checkPrefixCuts (2^48) 4845862913 10 Manual.Count131072.C036941.packed 64 cuts36941 = true := by
 decide +kernel
def pointBounds36941 : List (Nat × Nat × Nat) := [(4845987840,107865016949422,107865401852429)]
theorem point_links_checked36941 : (cuts36941.take 1).map (fun c => (4845862913-1+2*2^10*c.k,107864693010185+c.lower,107865077912997+c.upper)) = pointBounds36941 := by
 decide +kernel
def cuts36942 : List PrefixCut := [⟨64,336418190,336418397⟩]
theorem checked36942 : checkPrefixCuts (2^48) 4845993985 10 Manual.Count131072.C036942.packed 64 cuts36942 = true := by
 decide +kernel
def cuts36943 : List PrefixCut := [⟨7,36359569,36359591⟩,
⟨64,341520274,341520483⟩]
theorem checked36943 : checkPrefixCuts (2^48) 4846125057 10 Manual.Count131072.C036943.packed 64 cuts36943 = true := by
 decide +kernel
def pointBounds36943 : List (Nat × Nat × Nat) := [(4846139392,107865406339226,107865791242472)]
theorem point_links_checked36943 : (cuts36943.take 1).map (fun c => (4846125057-1+2*2^10*c.k,107865369979657+c.lower,107865754882881+c.upper)) = pointBounds36943 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000216
