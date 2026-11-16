import PlattAssemblyKernel
import PlattCertificates.Count131072.C024992
import PlattCertificates.Count131072.C024993
import PlattCertificates.Count131072.C024994
import PlattCertificates.Count131072.C024995
import PlattCertificates.Count131072.C024996
import PlattCertificates.Count131072.C024997
import PlattCertificates.Count131072.C024998
import PlattCertificates.Count131072.C024999
import PlattCertificates.Count131072.C025000
import PlattCertificates.Count131072.C025001
import PlattCertificates.Count131072.C025002
import PlattCertificates.Count131072.C025003
import PlattCertificates.Count131072.C025004
import PlattCertificates.Count131072.C025005
import PlattCertificates.Count131072.C025006
import PlattCertificates.Count131072.C025007
import PlattCertificates.Count131072.C025008
import PlattCertificates.Count131072.C025009
import PlattCertificates.Count131072.C025010
import PlattCertificates.Count131072.C025011
import PlattCertificates.Count131072.C025012
import PlattCertificates.Count131072.C025013
import PlattCertificates.Count131072.C025014
import PlattCertificates.Count131072.C025015
import PlattCertificates.Count131072.C025016
import PlattCertificates.Count131072.C025017
import PlattCertificates.Count131072.C025018
import PlattCertificates.Count131072.C025019
import PlattCertificates.Count131072.C025020
import PlattCertificates.Count131072.C025021
import PlattCertificates.Count131072.C025022
import PlattCertificates.Count131072.C025023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24992 : List PrefixCut := [⟨75,297805100,297805261⟩,
⟨128,507980931,507981209⟩]
theorem checked24992 : checkPrefixCuts (2^48) 3279683585 9 Manual.Count131072.C024992.packed 128 cuts24992 = true := by
 decide +kernel
def pointBounds24992 : List (Nat × Nat × Nat) := [(3279760384,102894203449477,102894585463836)]
theorem point_links_checked24992 : (cuts24992.take 1).map (fun c => (3279683585-1+2*2^9*c.k,102893905644377+c.lower,102894287658575+c.upper)) = pointBounds24992 := by
 decide +kernel
def cuts24993 : List PrefixCut := [⟨48,192665308,192665416⟩,
⟨128,513796346,513796633⟩]
theorem checked24993 : checkPrefixCuts (2^48) 3279814657 9 Manual.Count131072.C024993.packed 128 cuts24993 = true := by
 decide +kernel
def pointBounds24993 : List (Nat × Nat × Nat) := [(3279863808,102894606290616,102894988305200)]
theorem point_links_checked24993 : (cuts24993.take 1).map (fun c => (3279814657-1+2*2^9*c.k,102894413625308+c.lower,102894795639784+c.upper)) = pointBounds24993 := by
 decide +kernel
def cuts24994 : List PrefixCut := [⟨21,86674822,86674870⟩,
⟨122,486401151,486401425⟩,
⟨128,512059414,512059702⟩]
theorem checked24994 : checkPrefixCuts (2^48) 3279945729 9 Manual.Count131072.C024994.packed 128 cuts24994 = true := by
 decide +kernel
def pointBounds24994 : List (Nat × Nat × Nat) := [(3279967232,102895014096476,102895396111287),(3280070656,102895413822805,102895795837842)]
theorem point_links_checked24994 : (cuts24994.take 2).map (fun c => (3279945729-1+2*2^9*c.k,102894927421654+c.lower,102895309436417+c.upper)) = pointBounds24994 := by
 decide +kernel
def cuts24995 : List PrefixCut := [⟨95,381778600,381778808⟩,
⟨128,510322761,510323041⟩]
theorem checked24995 : checkPrefixCuts (2^48) 3280076801 9 Manual.Count131072.C024995.packed 128 cuts24995 = true := by
 decide +kernel
def pointBounds24995 : List (Nat × Nat × Nat) := [(3280174080,102895821259668,102896203274927)]
theorem point_links_checked24995 : (cuts24995.take 1).map (fun c => (3280076801-1+2*2^9*c.k,102895439481068+c.lower,102895821496119+c.upper)) = pointBounds24995 := by
 decide +kernel
def cuts24996 : List PrefixCut := [⟨68,273559603,273559754⟩,
⟨128,510302372,510302652⟩]
theorem checked24996 : checkPrefixCuts (2^48) 3280207873 9 Manual.Count131072.C024996.packed 128 cuts24996 = true := by
 decide +kernel
def pointBounds24996 : List (Nat × Nat × Nat) := [(3280277504,102896223363432,102896605378914)]
theorem point_links_checked24996 : (cuts24996.take 1).map (fun c => (3280207873-1+2*2^9*c.k,102895949803829+c.lower,102896331819160+c.upper)) = pointBounds24996 := by
 decide +kernel
def cuts24997 : List PrefixCut := [⟨41,162774174,162774269⟩,
⟨128,508480058,508480354⟩]
theorem checked24997 : checkPrefixCuts (2^48) 3280338945 9 Manual.Count131072.C024997.packed 128 cuts24997 = true := by
 decide +kernel
def pointBounds24997 : List (Nat × Nat × Nat) := [(3280380928,102896622880375,102897004896081)]
theorem point_links_checked24997 : (cuts24997.take 1).map (fun c => (3280338945-1+2*2^9*c.k,102896460106201+c.lower,102896842121812+c.upper)) = pointBounds24997 := by
 decide +kernel
def cuts24998 : List PrefixCut := [⟨14,58517665,58517700⟩,
⟨115,467104399,467104658⟩,
⟨128,519270777,519271067⟩]
theorem checked24998 : checkPrefixCuts (2^48) 3280470017 9 Manual.Count131072.C024998.packed 128 cuts24998 = true := by
 decide +kernel
def pointBounds24998 : List (Nat × Nat × Nat) := [(3280484352,102897027103924,102897409119866),(3280587776,102897435690658,102897817706824)]
theorem point_links_checked24998 : (cuts24998.take 2).map (fun c => (3280470017-1+2*2^9*c.k,102896968586259+c.lower,102897350602166+c.upper)) = pointBounds24998 := by
 decide +kernel
def cuts24999 : List PrefixCut := [⟨88,356150083,356150274⟩,
⟨128,515646543,515646818⟩]
theorem checked24999 : checkPrefixCuts (2^48) 3280601089 9 Manual.Count131072.C024999.packed 128 cuts24999 = true := by
 decide +kernel
def pointBounds24999 : List (Nat × Nat × Nat) := [(3280691200,102897844007119,102898226023507)]
theorem point_links_checked24999 : (cuts24999.take 1).map (fun c => (3280601089-1+2*2^9*c.k,102897487857036+c.lower,102897869873233+c.upper)) = pointBounds24999 := by
 decide +kernel
def cuts25000 : List PrefixCut := [⟨61,246404850,246404986⟩,
⟨128,517084342,517084625⟩]
theorem checked25000 : checkPrefixCuts (2^48) 3280732161 9 Manual.Count131072.C025000.packed 128 cuts25000 = true := by
 decide +kernel
def pointBounds25000 : List (Nat × Nat × Nat) := [(3280794624,102898249908429,102898631925037)]
theorem point_links_checked25000 : (cuts25000.take 1).map (fun c => (3280732161-1+2*2^9*c.k,102898003503579+c.lower,102898385520051+c.upper)) = pointBounds25000 := by
 decide +kernel
def cuts25001 : List PrefixCut := [⟨34,137182178,137182254⟩,
⟨128,510114631,510114919⟩]
theorem checked25001 : checkPrefixCuts (2^48) 3280863233 9 Manual.Count131072.C025001.packed 128 cuts25001 = true := by
 decide +kernel
def pointBounds25001 : List (Nat × Nat × Nat) := [(3280898048,102898657770099,102899039786930)]
theorem point_links_checked25001 : (cuts25001.take 1).map (fun c => (3280863233-1+2*2^9*c.k,102898520587921+c.lower,102898902604676+c.upper)) = pointBounds25001 := by
 decide +kernel
def cuts25002 : List PrefixCut := [⟨7,27709982,27709997⟩,
⟨108,433658714,433658957⟩,
⟨128,513354231,513354519⟩]
theorem checked25002 : checkPrefixCuts (2^48) 3280994305 9 Manual.Count131072.C025002.packed 128 cuts25002 = true := by
 decide +kernel
def pointBounds25002 : List (Nat × Nat × Nat) := [(3281001472,102899058412534,102899440429592),(3281104896,102899464361266,102899846378552)]
theorem point_links_checked25002 : (cuts25002.take 2).map (fun c => (3280994305-1+2*2^9*c.k,102899030702552+c.lower,102899412719595+c.upper)) = pointBounds25002 := by
 decide +kernel
def cuts25003 : List PrefixCut := [⟨81,322465790,322465972⟩,
⟨128,506470930,506471224⟩]
theorem checked25003 : checkPrefixCuts (2^48) 3281125377 9 Manual.Count131072.C025003.packed 128 cuts25003 = true := by
 decide +kernel
def pointBounds25003 : List (Nat × Nat × Nat) := [(3281208320,102899866522573,102900248540086)]
theorem point_links_checked25003 : (cuts25003.take 1).map (fun c => (3281125377-1+2*2^9*c.k,102899544056783+c.lower,102899926074114+c.upper)) = pointBounds25003 := by
 decide +kernel
def cuts25004 : List PrefixCut := [⟨54,214197501,214197623⟩,
⟨128,514170911,514171199⟩]
theorem checked25004 : checkPrefixCuts (2^48) 3281256449 9 Manual.Count131072.C025004.packed 128 cuts25004 = true := by
 decide +kernel
def pointBounds25004 : List (Nat × Nat × Nat) := [(3281311744,102900264725214,102900646742961)]
theorem point_links_checked25004 : (cuts25004.take 1).map (fun c => (3281256449-1+2*2^9*c.k,102900050527713+c.lower,102900432545338+c.upper)) = pointBounds25004 := by
 decide +kernel
def cuts25005 : List PrefixCut := [⟨27,111426747,111426809⟩,
⟨128,518439380,518439671⟩]
theorem checked25005 : checkPrefixCuts (2^48) 3281387521 9 Manual.Count131072.C025005.packed 128 cuts25005 = true := by
 decide +kernel
def pointBounds25005 : List (Nat × Nat × Nat) := [(3281415168,102900676125371,102901058143346),(3281518592,102901083138004,102901465156208)]
theorem point_links_checked25005 : (cuts25005.take 2).map (fun c => (3281387521-1+2*2^9*c.k,102900564698624+c.lower,102900946716537+c.upper)) = pointBounds25005 := by
 decide +kernel
def cuts25006 : List PrefixCut := [⟨101,398593938,398594162⟩,
⟨128,509412320,509412606⟩]
theorem checked25006 : checkPrefixCuts (2^48) 3281518593 9 Manual.Count131072.C025006.packed 128 cuts25006 = true := by
 decide +kernel
def pointBounds25006 : List (Nat × Nat × Nat) := [(3281622016,102901481731942,102901863750370)]
theorem point_links_checked25006 : (cuts25006.take 1).map (fun c => (3281518593-1+2*2^9*c.k,102901083138004+c.lower,102901465156208+c.upper)) = pointBounds25006 := by
 decide +kernel
def cuts25007 : List PrefixCut := [⟨74,299856808,299856979⟩,
⟨128,517969106,517969398⟩]
theorem checked25007 : checkPrefixCuts (2^48) 3281649665 9 Manual.Count131072.C025007.packed 128 cuts25007 = true := by
 decide +kernel
def pointBounds25007 : List (Nat × Nat × Nat) := [(3281725440,102901892407132,102902274425793)]
theorem point_links_checked25007 : (cuts25007.take 1).map (fun c => (3281649665-1+2*2^9*c.k,102901592550324+c.lower,102901974568814+c.upper)) = pointBounds25007 := by
 decide +kernel
def cuts25008 : List PrefixCut := [⟨47,184659210,184659309⟩,
⟨128,511258461,511258738⟩]
theorem checked25008 : checkPrefixCuts (2^48) 3281780737 9 Manual.Count131072.C025008.packed 128 cuts25008 = true := by
 decide +kernel
def pointBounds25008 : List (Nat × Nat × Nat) := [(3281828864,102902295178640,102902677197521)]
theorem point_links_checked25008 : (cuts25008.take 1).map (fun c => (3281780737-1+2*2^9*c.k,102902110519430+c.lower,102902492538212+c.upper)) = pointBounds25008 := by
 decide +kernel
def cuts25009 : List PrefixCut := [⟨20,83706896,83706943⟩,
⟨121,489368948,489369219⟩,
⟨128,515440655,515440941⟩]
theorem checked25009 : checkPrefixCuts (2^48) 3281911809 9 Manual.Count131072.C025009.packed 128 cuts25009 = true := by
 decide +kernel
def pointBounds25009 : List (Nat × Nat × Nat) := [(3281932288,102902705484787,102903087503893),(3282035712,102903111146839,102903493166169)]
theorem point_links_checked25009 : (cuts25009.take 2).map (fun c => (3281911809-1+2*2^9*c.k,102902621777891+c.lower,102903003796950+c.upper)) = pointBounds25009 := by
 decide +kernel
def cuts25010 : List PrefixCut := [⟨94,378891411,378891622⟩,
⟨128,513275970,513276257⟩]
theorem checked25010 : checkPrefixCuts (2^48) 3282042881 9 Manual.Count131072.C025010.packed 128 cuts25010 = true := by
 decide +kernel
def pointBounds25010 : List (Nat × Nat × Nat) := [(3282139136,102903516109957,102903898129513)]
theorem point_links_checked25010 : (cuts25010.take 1).map (fun c => (3282042881-1+2*2^9*c.k,102903137218546+c.lower,102903519237891+c.upper)) = pointBounds25010 := by
 decide +kernel
def cuts25011 : List PrefixCut := [⟨67,265677607,265677758⟩,
⟨128,504508243,504508530⟩]
theorem checked25011 : checkPrefixCuts (2^48) 3282173953 9 Manual.Count131072.C025011.packed 128 cuts25011 = true := by
 decide +kernel
def pointBounds25011 : List (Nat × Nat × Nat) := [(3282242560,102903916172123,102904298191906)]
theorem point_links_checked25011 : (cuts25011.take 1).map (fun c => (3282173953-1+2*2^9*c.k,102903650494516+c.lower,102904032514148+c.upper)) = pointBounds25011 := by
 decide +kernel
def cuts25012 : List PrefixCut := [⟨40,159418028,159418119⟩,
⟨128,508003960,508004243⟩]
theorem checked25012 : checkPrefixCuts (2^48) 3282305025 9 Manual.Count131072.C025012.packed 128 cuts25012 = true := by
 decide +kernel
def pointBounds25012 : List (Nat × Nat × Nat) := [(3282345984,102904314420787,102904696440797)]
theorem point_links_checked25012 : (cuts25012.take 1).map (fun c => (3282305025-1+2*2^9*c.k,102904155002759+c.lower,102904537022678+c.upper)) = pointBounds25012 := by
 decide +kernel
def cuts25013 : List PrefixCut := [⟨13,55395570,55395601⟩,
⟨114,458078129,458078393⟩,
⟨128,515272438,515272735⟩]
theorem checked25013 : checkPrefixCuts (2^48) 3282436097 9 Manual.Count131072.C025013.packed 128 cuts25013 = true := by
 decide +kernel
def pointBounds25013 : List (Nat × Nat × Nat) := [(3282449408,102904718402289,102905100422522),(3282552832,102905121084848,102905503105314)]
theorem point_links_checked25013 : (cuts25013.take 2).map (fun c => (3282436097-1+2*2^9*c.k,102904663006719+c.lower,102905045026921+c.upper)) = pointBounds25013 := by
 decide +kernel
def cuts25014 : List PrefixCut := [⟨87,345475673,345475864⟩,
⟨128,512936710,512936991⟩]
theorem checked25014 : checkPrefixCuts (2^48) 3282567169 9 Manual.Count131072.C025014.packed 128 cuts25014 = true := by
 decide +kernel
def pointBounds25014 : List (Nat × Nat × Nat) := [(3282656256,102905523754830,102905905775520)]
theorem point_links_checked25014 : (cuts25014.take 1).map (fun c => (3282567169-1+2*2^9*c.k,102905178279157+c.lower,102905560299656+c.upper)) = pointBounds25014 := by
 decide +kernel
def cuts25015 : List PrefixCut := [⟨60,240941159,240941292⟩,
⟨128,516946138,516946424⟩]
theorem checked25015 : checkPrefixCuts (2^48) 3282698241 9 Manual.Count131072.C025015.packed 128 cuts25015 = true := by
 decide +kernel
def pointBounds25015 : List (Nat × Nat × Nat) := [(3282759680,102905932157026,102906314177939)]
theorem point_links_checked25015 : (cuts25015.take 1).map (fun c => (3282698241-1+2*2^9*c.k,102905691215867+c.lower,102906073236647+c.upper)) = pointBounds25015 := by
 decide +kernel
def cuts25016 : List PrefixCut := [⟨33,130326490,130326568⟩,
⟨128,514610472,514610769⟩]
theorem checked25016 : checkPrefixCuts (2^48) 3282829313 9 Manual.Count131072.C025016.packed 128 cuts25016 = true := by
 decide +kernel
def pointBounds25016 : List (Nat × Nat × Nat) := [(3282863104,102906338488495,102906720509639)]
theorem point_links_checked25016 : (cuts25016.take 1).map (fun c => (3282829313-1+2*2^9*c.k,102906208162005+c.lower,102906590183071+c.upper)) = pointBounds25016 := by
 decide +kernel
def cuts25017 : List PrefixCut := [⟨6,25035511,25035526⟩,
⟨107,430141055,430141298⟩,
⟨128,515447374,515447662⟩]
theorem checked25017 : checkPrefixCuts (2^48) 3282960385 9 Manual.Count131072.C025017.packed 128 cuts25017 = true := by
 decide +kernel
def pointBounds25017 : List (Nat × Nat × Nat) := [(3282966528,102906747807988,102907129829366),(3283069952,102907152913532,102907534935138)]
theorem point_links_checked25017 : (cuts25017.take 2).map (fun c => (3282960385-1+2*2^9*c.k,102906722772477+c.lower,102907104793840+c.upper)) = pointBounds25017 := by
 decide +kernel
def cuts25018 : List PrefixCut := [⟨80,321072448,321072631⟩,
⟨128,511568808,511569097⟩]
theorem checked25018 : checkPrefixCuts (2^48) 3283091457 9 Manual.Count131072.C025018.packed 128 cuts25018 = true := by
 decide +kernel
def pointBounds25018 : List (Nat × Nat × Nat) := [(3283173376,102907559292299,102907941314133)]
theorem point_links_checked25018 : (cuts25018.take 1).map (fun c => (3283091457-1+2*2^9*c.k,102907238219851+c.lower,102907620241502+c.upper)) = pointBounds25018 := by
 decide +kernel
def cuts25019 : List PrefixCut := [⟨53,213469151,213469267⟩,
⟨128,511548410,511548696⟩]
theorem checked25019 : checkPrefixCuts (2^48) 3283222529 9 Manual.Count131072.C025019.packed 128 cuts25019 = true := by
 decide +kernel
def pointBounds25019 : List (Nat × Nat × Nat) := [(3283276800,102907963257810,102908345279866)]
theorem point_links_checked25019 : (cuts25019.take 1).map (fun c => (3283222529-1+2*2^9*c.k,102907749788659+c.lower,102908131810599+c.upper)) = pointBounds25019 := by
 decide +kernel
def cuts25020 : List PrefixCut := [⟨26,103901760,103901818⟩,
⟨127,506213057,506213347⟩,
⟨128,510670729,510671021⟩]
theorem checked25020 : checkPrefixCuts (2^48) 3283353601 9 Manual.Count131072.C025020.packed 128 cuts25020 = true := by
 decide +kernel
def pointBounds25020 : List (Nat × Nat × Nat) := [(3283380224,102908365238829,102908747261113),(3283483648,102908767550126,102909149572642)]
theorem point_links_checked25020 : (cuts25020.take 2).map (fun c => (3283353601-1+2*2^9*c.k,102908261337069+c.lower,102908643359295+c.upper)) = pointBounds25020 := by
 decide +kernel
def cuts25021 : List PrefixCut := [⟨100,402984307,402984537⟩,
⟨128,513393468,513393755⟩]
theorem checked25021 : checkPrefixCuts (2^48) 3283484673 9 Manual.Count131072.C025021.packed 128 cuts25021 = true := by
 decide +kernel
def pointBounds25021 : List (Nat × Nat × Nat) := [(3283587072,102909174992105,102909557014853)]
theorem point_links_checked25021 : (cuts25021.take 1).map (fun c => (3283484673-1+2*2^9*c.k,102908772007798+c.lower,102909154030316+c.upper)) = pointBounds25021 := by
 decide +kernel
def cuts25022 : List PrefixCut := [⟨73,289990945,289991107⟩,
⟨128,510115630,510115918⟩]
theorem checked25022 : checkPrefixCuts (2^48) 3283615745 9 Manual.Count131072.C025022.packed 128 cuts25022 = true := by
 decide +kernel
def pointBounds25022 : List (Nat × Nat × Nat) := [(3283690496,102909575392211,102909957415178)]
theorem point_links_checked25022 : (cuts25022.take 1).map (fun c => (3283615745-1+2*2^9*c.k,102909285401266+c.lower,102909667424071+c.upper)) = pointBounds25022 := by
 decide +kernel
def cuts25023 : List PrefixCut := [⟨46,187720178,187720277⟩,
⟨128,511723979,511724266⟩]
theorem checked25023 : checkPrefixCuts (2^48) 3283746817 9 Manual.Count131072.C025023.packed 128 cuts25023 = true := by
 decide +kernel
def pointBounds25023 : List (Nat × Nat × Nat) := [(3283793920,102909983237074,102910365260266)]
theorem point_links_checked25023 : (cuts25023.take 1).map (fun c => (3283746817-1+2*2^9*c.k,102909795516896+c.lower,102910177539989+c.upper)) = pointBounds25023 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000156
