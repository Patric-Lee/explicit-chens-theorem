import PlattAssemblyKernel
import PlattCertificates.Count131072.C029600
import PlattCertificates.Count131072.C029601
import PlattCertificates.Count131072.C029602
import PlattCertificates.Count131072.C029603
import PlattCertificates.Count131072.C029604
import PlattCertificates.Count131072.C029605
import PlattCertificates.Count131072.C029606
import PlattCertificates.Count131072.C029607
import PlattCertificates.Count131072.C029608
import PlattCertificates.Count131072.C029609
import PlattCertificates.Count131072.C029610
import PlattCertificates.Count131072.C029611
import PlattCertificates.Count131072.C029612
import PlattCertificates.Count131072.C029613
import PlattCertificates.Count131072.C029614
import PlattCertificates.Count131072.C029615
import PlattCertificates.Count131072.C029616
import PlattCertificates.Count131072.C029617
import PlattCertificates.Count131072.C029618
import PlattCertificates.Count131072.C029619
import PlattCertificates.Count131072.C029620
import PlattCertificates.Count131072.C029621
import PlattCertificates.Count131072.C029622
import PlattCertificates.Count131072.C029623
import PlattCertificates.Count131072.C029624
import PlattCertificates.Count131072.C029625
import PlattCertificates.Count131072.C029626
import PlattCertificates.Count131072.C029627
import PlattCertificates.Count131072.C029628
import PlattCertificates.Count131072.C029629
import PlattCertificates.Count131072.C029630
import PlattCertificates.Count131072.C029631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000300
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29600 : List PrefixCut := [⟨62,212499794,212499913⟩,
⟨128,436881884,436882124⟩]
theorem checked29600 : checkPrefixCuts (2^48) 3883663361 9 Manual.Count131072.C029600.packed 128 cuts29600 = true := by
 decide +kernel
def pointBounds29600 : List (Nat × Nat × Nat) := [(3883726848,105057345863817,105057729089271)]
theorem point_links_checked29600 : (cuts29600.take 1).map (fun c => (3883663361-1+2*2^9*c.k,105057133364023+c.lower,105057516589358+c.upper)) = pointBounds29600 := by
 decide +kernel
def cuts29601 : List PrefixCut := [⟨53,180024670,180024767⟩,
⟨128,428677709,428677950⟩]
theorem checked29601 : checkPrefixCuts (2^48) 3883794433 9 Manual.Count131072.C029601.packed 128 cuts29601 = true := by
 decide +kernel
def pointBounds29601 : List (Nat × Nat × Nat) := [(3883848704,105057750270577,105058133496249)]
theorem point_links_checked29601 : (cuts29601.take 1).map (fun c => (3883794433-1+2*2^9*c.k,105057570245907+c.lower,105057953471482+c.upper)) = pointBounds29601 := by
 decide +kernel
def cuts29602 : List PrefixCut := [⟨44,149001067,149001153⟩,
⟨128,431344608,431344852⟩]
theorem checked29602 : checkPrefixCuts (2^48) 3883925505 9 Manual.Count131072.C029602.packed 128 cuts29602 = true := by
 decide +kernel
def pointBounds29602 : List (Nat × Nat × Nat) := [(3883970560,105058147924683,105058531150585)]
theorem point_links_checked29602 : (cuts29602.take 1).map (fun c => (3883925505-1+2*2^9*c.k,105057998923616+c.lower,105058382149432+c.upper)) = pointBounds29602 := by
 decide +kernel
def cuts29603 : List PrefixCut := [⟨35,116819991,116820058⟩,
⟨128,424735442,424735687⟩]
theorem checked29603 : checkPrefixCuts (2^48) 3884056577 9 Manual.Count131072.C029603.packed 128 cuts29603 = true := by
 decide +kernel
def pointBounds29603 : List (Nat × Nat × Nat) := [(3884092416,105058547088215,105058930314342)]
theorem point_links_checked29603 : (cuts29603.take 1).map (fun c => (3884056577-1+2*2^9*c.k,105058430268224+c.lower,105058813494284+c.upper)) = pointBounds29603 := by
 decide +kernel
def cuts29604 : List PrefixCut := [⟨26,90148477,90148525⟩,
⟨128,436098316,436098556⟩]
theorem checked29604 : checkPrefixCuts (2^48) 3884187649 9 Manual.Count131072.C029604.packed 128 cuts29604 = true := by
 decide +kernel
def pointBounds29604 : List (Nat × Nat × Nat) := [(3884214272,105058945152143,105059328378496)]
theorem point_links_checked29604 : (cuts29604.take 1).map (fun c => (3884187649-1+2*2^9*c.k,105058855003666+c.lower,105059238229971+c.upper)) = pointBounds29604 := by
 decide +kernel
def cuts29605 : List PrefixCut := [⟨17,56594583,56594614⟩,
⟨128,432532809,432533051⟩]
theorem checked29605 : checkPrefixCuts (2^48) 3884318721 9 Manual.Count131072.C029605.packed 128 cuts29605 = true := by
 decide +kernel
def pointBounds29605 : List (Nat × Nat × Nat) := [(3884336128,105059347696565,105059730923141)]
theorem point_links_checked29605 : (cuts29605.take 1).map (fun c => (3884318721-1+2*2^9*c.k,105059291101982+c.lower,105059674328527+c.upper)) = pointBounds29605 := by
 decide +kernel
def cuts29606 : List PrefixCut := [⟨8,26448593,26448608⟩,
⟨127,426431555,426431792⟩,
⟨128,429547315,429547554⟩]
theorem checked29606 : checkPrefixCuts (2^48) 3884449793 9 Manual.Count131072.C029606.packed 128 cuts29606 = true := by
 decide +kernel
def pointBounds29606 : List (Nat × Nat × Nat) := [(3884457984,105059750083384,105060133310186),(3884579840,105060150066346,105060533293370)]
theorem point_links_checked29606 : (cuts29606.take 2).map (fun c => (3884449793-1+2*2^9*c.k,105059723634791+c.lower,105060106861578+c.upper)) = pointBounds29606 := by
 decide +kernel
def cuts29607 : List PrefixCut := [⟨118,396709787,396710007⟩,
⟨128,429822719,429822958⟩]
theorem checked29607 : checkPrefixCuts (2^48) 3884580865 9 Manual.Count131072.C029607.packed 128 cuts29607 = true := by
 decide +kernel
def pointBounds29607 : List (Nat × Nat × Nat) := [(3884701696,105060549891893,105060933119139)]
theorem point_links_checked29607 : (cuts29607.take 1).map (fun c => (3884580865-1+2*2^9*c.k,105060153182106+c.lower,105060536409132+c.upper)) = pointBounds29607 := by
 decide +kernel
def cuts29608 : List PrefixCut := [⟨109,367714389,367714599⟩,
⟨128,429663258,429663503⟩]
theorem checked29608 : checkPrefixCuts (2^48) 3884711937 9 Manual.Count131072.C029608.packed 128 cuts29608 = true := by
 decide +kernel
def pointBounds29608 : List (Nat × Nat × Nat) := [(3884823552,105060950719214,105061333946689)]
theorem point_links_checked29608 : (cuts29608.take 1).map (fun c => (3884711937-1+2*2^9*c.k,105060583004825+c.lower,105060966232090+c.upper)) = pointBounds29608 := by
 decide +kernel
def cuts29609 : List PrefixCut := [⟨100,339228155,339228349⟩,
⟨128,432474472,432474717⟩]
theorem checked29609 : checkPrefixCuts (2^48) 3884843009 9 Manual.Count131072.C029609.packed 128 cuts29609 = true := by
 decide +kernel
def pointBounds29609 : List (Nat × Nat × Nat) := [(3884945408,105061351896238,105061735123942)]
theorem point_links_checked29609 : (cuts29609.take 1).map (fun c => (3884843009-1+2*2^9*c.k,105061012668083+c.lower,105061395895593+c.upper)) = pointBounds29609 := by
 decide +kernel
def cuts29610 : List PrefixCut := [⟨91,301832218,301832392⟩,
⟨128,424707590,424707832⟩]
theorem checked29610 : checkPrefixCuts (2^48) 3884974081 9 Manual.Count131072.C029610.packed 128 cuts29610 = true := by
 decide +kernel
def pointBounds29610 : List (Nat × Nat × Nat) := [(3885067264,105061746974773,105062130202702)]
theorem point_links_checked29610 : (cuts29610.take 1).map (fun c => (3884974081-1+2*2^9*c.k,105061445142555+c.lower,105061828370310+c.upper)) = pointBounds29610 := by
 decide +kernel
def cuts29611 : List PrefixCut := [⟨82,272697918,272698071⟩,
⟨128,429474843,429475077⟩]
theorem checked29611 : checkPrefixCuts (2^48) 3885105153 9 Manual.Count131072.C029611.packed 128 cuts29611 = true := by
 decide +kernel
def pointBounds29611 : List (Nat × Nat × Nat) := [(3885189120,105062142548063,105062525776213)]
theorem point_links_checked29611 : (cuts29611.take 1).map (fun c => (3885105153-1+2*2^9*c.k,105061869850145+c.lower,105062253078142+c.upper)) = pointBounds29611 := by
 decide +kernel
def cuts29612 : List PrefixCut := [⟨73,244652200,244652339⟩,
⟨128,430257275,430257514⟩]
theorem checked29612 : checkPrefixCuts (2^48) 3885236225 9 Manual.Count131072.C029612.packed 128 cuts29612 = true := by
 decide +kernel
def pointBounds29612 : List (Nat × Nat × Nat) := [(3885310976,105062543977188,105062927205558)]
theorem point_links_checked29612 : (cuts29612.take 1).map (fun c => (3885236225-1+2*2^9*c.k,105062299324988+c.lower,105062682553219+c.upper)) = pointBounds29612 := by
 decide +kernel
def cuts29613 : List PrefixCut := [⟨64,216753190,216753313⟩,
⟨128,430170365,430170611⟩]
theorem checked29613 : checkPrefixCuts (2^48) 3885367297 9 Manual.Count131072.C029613.packed 128 cuts29613 = true := by
 decide +kernel
def pointBounds29613 : List (Nat × Nat × Nat) := [(3885432832,105062946335453,105063329564046)]
theorem point_links_checked29613 : (cuts29613.take 1).map (fun c => (3885367297-1+2*2^9*c.k,105062729582263+c.lower,105063112810733+c.upper)) = pointBounds29613 := by
 decide +kernel
def cuts29614 : List PrefixCut := [⟨55,188421345,188421452⟩,
⟨128,435661316,435661561⟩]
theorem checked29614 : checkPrefixCuts (2^48) 3885498369 9 Manual.Count131072.C029614.packed 128 cuts29614 = true := by
 decide +kernel
def pointBounds29614 : List (Nat × Nat × Nat) := [(3885554688,105063348173973,105063731402796)]
theorem point_links_checked29614 : (cuts29614.take 1).map (fun c => (3885498369-1+2*2^9*c.k,105063159752628+c.lower,105063542981344+c.upper)) = pointBounds29614 := by
 decide +kernel
def cuts29615 : List PrefixCut := [⟨46,150674233,150674320⟩,
⟨128,424346183,424346424⟩]
theorem checked29615 : checkPrefixCuts (2^48) 3885629441 9 Manual.Count131072.C029615.packed 128 cuts29615 = true := by
 decide +kernel
def pointBounds29615 : List (Nat × Nat × Nat) := [(3885676544,105063746088177,105064129317225)]
theorem point_links_checked29615 : (cuts29615.take 1).map (fun c => (3885629441-1+2*2^9*c.k,105063595413944+c.lower,105063978642905+c.upper)) = pointBounds29615 := by
 decide +kernel
def cuts29616 : List PrefixCut := [⟨37,124591952,124592024⟩,
⟨128,429619744,429619989⟩]
theorem checked29616 : checkPrefixCuts (2^48) 3885760513 9 Manual.Count131072.C029616.packed 128 cuts29616 = true := by
 decide +kernel
def pointBounds29616 : List (Nat × Nat × Nat) := [(3885798400,105064144352079,105064527581353)]
theorem point_links_checked29616 : (cuts29616.take 1).map (fun c => (3885760513-1+2*2^9*c.k,105064019760127+c.lower,105064402989329+c.upper)) = pointBounds29616 := by
 decide +kernel
def cuts29617 : List PrefixCut := [⟨28,95324224,95324276⟩,
⟨128,430619381,430619619⟩]
theorem checked29617 : checkPrefixCuts (2^48) 3885891585 9 Manual.Count131072.C029617.packed 128 cuts29617 = true := by
 decide +kernel
def pointBounds29617 : List (Nat × Nat × Nat) := [(3885920256,105064544704095,105064927933594)]
theorem point_links_checked29617 : (cuts29617.take 1).map (fun c => (3885891585-1+2*2^9*c.k,105064449379871+c.lower,105064832609318+c.upper)) = pointBounds29617 := by
 decide +kernel
def cuts29618 : List PrefixCut := [⟨19,64464897,64464931⟩,
⟨128,431618861,431619099⟩]
theorem checked29618 : checkPrefixCuts (2^48) 3886022657 9 Manual.Count131072.C029618.packed 128 cuts29618 = true := by
 decide +kernel
def pointBounds29618 : List (Nat × Nat × Nat) := [(3886042112,105064944464149,105065327693868)]
theorem point_links_checked29618 : (cuts29618.take 1).map (fun c => (3886022657-1+2*2^9*c.k,105064879999252+c.lower,105065263228937+c.upper)) = pointBounds29618 := by
 decide +kernel
def cuts29619 : List PrefixCut := [⟨10,35345893,35345913⟩,
⟨128,434573904,434574143⟩]
theorem checked29619 : checkPrefixCuts (2^48) 3886153729 9 Manual.Count131072.C029619.packed 128 cuts29619 = true := by
 decide +kernel
def pointBounds29619 : List (Nat × Nat × Nat) := [(3886163968,105065346964006,105065730193949)]
theorem point_links_checked29619 : (cuts29619.take 1).map (fun c => (3886153729-1+2*2^9*c.k,105065311618113+c.lower,105065694848036+c.upper)) = pointBounds29619 := by
 decide +kernel
def cuts29620 : List PrefixCut := [⟨1,3548960,3548962⟩,
⟨120,408630957,408631190⟩,
⟨128,435428352,435428599⟩]
theorem checked29620 : checkPrefixCuts (2^48) 3886284801 9 Manual.Count131072.C029620.packed 128 cuts29620 = true := by
 decide +kernel
def pointBounds29620 : List (Nat × Nat × Nat) := [(3886285824,105065749740977,105066132971141),(3886407680,105066154822974,105066538053369)]
theorem point_links_checked29620 : (cuts29620.take 2).map (fun c => (3886284801-1+2*2^9*c.k,105065746192017+c.lower,105066129422179+c.upper)) = pointBounds29620 := by
 decide +kernel
def cuts29621 : List PrefixCut := [⟨111,365380393,365380604⟩,
⟨128,423680935,423681180⟩]
theorem checked29621 : checkPrefixCuts (2^48) 3886415873 9 Manual.Count131072.C029621.packed 128 cuts29621 = true := by
 decide +kernel
def pointBounds29621 : List (Nat × Nat × Nat) := [(3886529536,105066547000762,105066930231382)]
theorem point_links_checked29621 : (cuts29621.take 1).map (fun c => (3886415873-1+2*2^9*c.k,105066181620369+c.lower,105066564850778+c.upper)) = pointBounds29621 := by
 decide +kernel
def cuts29622 : List PrefixCut := [⟨102,344800636,344800828⟩,
⟨128,431705451,431705693⟩]
theorem checked29622 : checkPrefixCuts (2^48) 3886546945 9 Manual.Count131072.C029622.packed 128 cuts29622 = true := by
 decide +kernel
def pointBounds29622 : List (Nat × Nat × Nat) := [(3886651392,105066950101940,105067333332786)]
theorem point_links_checked29622 : (cuts29622.take 1).map (fun c => (3886546945-1+2*2^9*c.k,105066605301304+c.lower,105066988531958+c.upper)) = pointBounds29622 := by
 decide +kernel
def cuts29623 : List PrefixCut := [⟨93,310317753,310317923⟩,
⟨128,428287217,428287452⟩]
theorem checked29623 : checkPrefixCuts (2^48) 3886678017 9 Manual.Count131072.C029623.packed 128 cuts29623 = true := by
 decide +kernel
def pointBounds29623 : List (Nat × Nat × Nat) := [(3886773248,105067347324508,105067730555574)]
theorem point_links_checked29623 : (cuts29623.take 1).map (fun c => (3886678017-1+2*2^9*c.k,105067037006755+c.lower,105067420237651+c.upper)) = pointBounds29623 := by
 decide +kernel
def cuts29624 : List PrefixCut := [⟨84,281340759,281340919⟩,
⟨128,426824450,426824693⟩]
theorem checked29624 : checkPrefixCuts (2^48) 3886809089 9 Manual.Count131072.C029624.packed 128 cuts29624 = true := by
 decide +kernel
def pointBounds29624 : List (Nat × Nat × Nat) := [(3886895104,105067746634731,105068129866022)]
theorem point_links_checked29624 : (cuts29624.take 1).map (fun c => (3886809089-1+2*2^9*c.k,105067465293972+c.lower,105067848525103+c.upper)) = pointBounds29624 := by
 decide +kernel
def cuts29625 : List PrefixCut := [⟨75,255551972,255552111⟩,
⟨128,431444638,431444876⟩]
theorem checked29625 : checkPrefixCuts (2^48) 3886940161 9 Manual.Count131072.C029625.packed 128 cuts29625 = true := by
 decide +kernel
def pointBounds29625 : List (Nat × Nat × Nat) := [(3887016960,105068147670394,105068530901907)]
theorem point_links_checked29625 : (cuts29625.take 1).map (fun c => (3886940161-1+2*2^9*c.k,105067892118422+c.lower,105068275349796+c.upper)) = pointBounds29625 := by
 decide +kernel
def cuts29626 : List PrefixCut := [⟨66,224913133,224913262⟩,
⟨128,431140396,431140641⟩]
theorem checked29626 : checkPrefixCuts (2^48) 3887071233 9 Manual.Count131072.C029626.packed 128 cuts29626 = true := by
 decide +kernel
def pointBounds29626 : List (Nat × Nat × Nat) := [(3887138816,105068548476193,105068931707934)]
theorem point_links_checked29626 : (cuts29626.take 1).map (fun c => (3887071233-1+2*2^9*c.k,105068323563060+c.lower,105068706794672+c.upper)) = pointBounds29626 := by
 decide +kernel
def cuts29627 : List PrefixCut := [⟨57,191162711,191162821⟩,
⟨128,421929839,421930080⟩]
theorem checked29627 : checkPrefixCuts (2^48) 3887202305 9 Manual.Count131072.C029627.packed 128 cuts29627 = true := by
 decide +kernel
def pointBounds29627 : List (Nat × Nat × Nat) := [(3887260672,105068945866167,105069329098134)]
theorem point_links_checked29627 : (cuts29627.take 1).map (fun c => (3887202305-1+2*2^9*c.k,105068754703456+c.lower,105069137935313+c.upper)) = pointBounds29627 := by
 decide +kernel
def cuts29628 : List PrefixCut := [⟨48,164003578,164003671⟩,
⟨128,430894084,430894324⟩]
theorem checked29628 : checkPrefixCuts (2^48) 3887333377 9 Manual.Count131072.C029628.packed 128 cuts29628 = true := by
 decide +kernel
def pointBounds29628 : List (Nat × Nat × Nat) := [(3887382528,105069340636873,105069723869064)]
theorem point_links_checked29628 : (cuts29628.take 1).map (fun c => (3887333377-1+2*2^9*c.k,105069176633295+c.lower,105069559865393+c.upper)) = pointBounds29628 := by
 decide +kernel
def cuts29629 : List PrefixCut := [⟨39,130257324,130257397⟩,
⟨128,428924568,428924813⟩]
theorem checked29629 : checkPrefixCuts (2^48) 3887464449 9 Manual.Count131072.C029629.packed 128 cuts29629 = true := by
 decide +kernel
def pointBounds29629 : List (Nat × Nat × Nat) := [(3887504384,105069737784703,105070121017114)]
theorem point_links_checked29629 : (cuts29629.take 1).map (fun c => (3887464449-1+2*2^9*c.k,105069607527379+c.lower,105069990759717+c.upper)) = pointBounds29629 := by
 decide +kernel
def cuts29630 : List PrefixCut := [⟨30,100133419,100133477⟩,
⟨128,425145244,425145487⟩]
theorem checked29630 : checkPrefixCuts (2^48) 3887595521 9 Manual.Count131072.C029630.packed 128 cuts29630 = true := by
 decide +kernel
def pointBounds29630 : List (Nat × Nat × Nat) := [(3887626240,105070136585366,105070519818007)]
theorem point_links_checked29630 : (cuts29630.take 1).map (fun c => (3887595521-1+2*2^9*c.k,105070036451947+c.lower,105070419684530+c.upper)) = pointBounds29630 := by
 decide +kernel
def cuts29631 : List PrefixCut := [⟨21,68056656,68056693⟩,
⟨128,431574416,431574658⟩]
theorem checked29631 : checkPrefixCuts (2^48) 3887726593 9 Manual.Count131072.C029631.packed 128 cuts29631 = true := by
 decide +kernel
def pointBounds29631 : List (Nat × Nat × Nat) := [(3887748096,105070529653847,105070912886710)]
theorem point_links_checked29631 : (cuts29631.take 1).map (fun c => (3887726593-1+2*2^9*c.k,105070461597191+c.lower,105070844830017+c.upper)) = pointBounds29631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000300
