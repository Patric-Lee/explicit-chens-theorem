import PlattAssemblyKernel
import PlattCertificates.Count131072.C018640
import PlattCertificates.Count131072.C018641
import PlattCertificates.Count131072.C018642
import PlattCertificates.Count131072.C018643
import PlattCertificates.Count131072.C018644
import PlattCertificates.Count131072.C018645
import PlattCertificates.Count131072.C018646
import PlattCertificates.Count131072.C018647
import PlattCertificates.Count131072.C018648
import PlattCertificates.Count131072.C018649
import PlattCertificates.Count131072.C018650
import PlattCertificates.Count131072.C018651
import PlattCertificates.Count131072.C018652
import PlattCertificates.Count131072.C018653
import PlattCertificates.Count131072.C018654
import PlattCertificates.Count131072.C018655
import PlattCertificates.Count131072.C018656
import PlattCertificates.Count131072.C018657
import PlattCertificates.Count131072.C018658
import PlattCertificates.Count131072.C018659
import PlattCertificates.Count131072.C018660
import PlattCertificates.Count131072.C018661
import PlattCertificates.Count131072.C018662
import PlattCertificates.Count131072.C018663
import PlattCertificates.Count131072.C018664
import PlattCertificates.Count131072.C018665
import PlattCertificates.Count131072.C018666
import PlattCertificates.Count131072.C018667
import PlattCertificates.Count131072.C018668
import PlattCertificates.Count131072.C018669
import PlattCertificates.Count131072.C018670
import PlattCertificates.Count131072.C018671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000270
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18640 : List PrefixCut := [⟨7,39682943,39682966⟩,
⟨82,444442012,444442278⟩,
⟨128,698862107,698862531⟩]
theorem checked18640 : checkPrefixCuts (2^48) 2447114241 9 Manual.Count131072.C018640.packed 128 cuts18640 = true := by
 decide +kernel
def pointBounds18640 : List (Nat × Nat × Nat) := [(2447121408,99106794505442,99107174331419),(2447198208,99107199264511,99107579090731)]
theorem point_links_checked18640 : (cuts18640.take 2).map (fun c => (2447114241-1+2*2^9*c.k,99106754822499+c.lower,99107134648453+c.upper)) = pointBounds18640 := by
 decide +kernel
def cuts18641 : List PrefixCut := [⟨29,153661829,153661923⟩,
⟨104,567136598,567136942⟩,
⟨128,698824705,698825128⟩]
theorem checked18641 : checkPrefixCuts (2^48) 2447245313 9 Manual.Count131072.C018641.packed 128 cuts18641 = true := by
 decide +kernel
def pointBounds18641 : List (Nat × Nat × Nat) := [(2447275008,99107607346435,99107987172907),(2447351808,99108020821204,99108400647926)]
theorem point_links_checked18641 : (cuts18641.take 2).map (fun c => (2447245313-1+2*2^9*c.k,99107453684606+c.lower,99107833510984+c.upper)) = pointBounds18641 := by
 decide +kernel
def cuts18642 : List PrefixCut := [⟨51,276138128,276138294⟩,
⟨126,687401784,687402193⟩,
⟨128,697867217,697867633⟩]
theorem checked18642 : checkPrefixCuts (2^48) 2447376385 9 Manual.Count131072.C018642.packed 128 cuts18642 = true := by
 decide +kernel
def pointBounds18642 : List (Nat × Nat × Nat) := [(2447428608,99108428647439,99108808474406),(2447505408,99108839911095,99109219738305)]
theorem point_links_checked18642 : (cuts18642.take 2).map (fun c => (2447376385-1+2*2^9*c.k,99108152509311+c.lower,99108532336112+c.upper)) = pointBounds18642 := by
 decide +kernel
def cuts18643 : List PrefixCut := [⟨73,398140300,398140545⟩,
⟨128,700474981,700475405⟩]
theorem checked18643 : checkPrefixCuts (2^48) 2447507457 9 Manual.Count131072.C018643.packed 128 cuts18643 = true := by
 decide +kernel
def pointBounds18643 : List (Nat × Nat × Nat) := [(2447582208,99109248516828,99109628344290)]
theorem point_links_checked18643 : (cuts18643.take 1).map (fun c => (2447507457-1+2*2^9*c.k,99108850376528+c.lower,99109230203745+c.upper)) = pointBounds18643 := by
 decide +kernel
def cuts18644 : List PrefixCut := [⟨20,108443174,108443240⟩,
⟨95,531972574,531972890⟩,
⟨128,707337208,707337631⟩]
theorem checked18644 : checkPrefixCuts (2^48) 2447638529 9 Manual.Count131072.C018644.packed 128 cuts18644 = true := by
 decide +kernel
def pointBounds18644 : List (Nat × Nat × Nat) := [(2447659008,99109659294683,99110039122390),(2447735808,99110082824083,99110462652040)]
theorem point_links_checked18644 : (cuts18644.take 2).map (fun c => (2447638529-1+2*2^9*c.k,99109550851509+c.lower,99109930679150+c.upper)) = pointBounds18644 := by
 decide +kernel
def cuts18645 : List PrefixCut := [⟨42,228372925,228373064⟩,
⟨117,638192136,638192515⟩,
⟨128,700859788,700860203⟩]
theorem checked18645 : checkPrefixCuts (2^48) 2447769601 9 Manual.Count131072.C018645.packed 128 cuts18645 = true := by
 decide +kernel
def pointBounds18645 : List (Nat × Nat × Nat) := [(2447812608,99110486561642,99110866389845),(2447889408,99110896380853,99111276209296)]
theorem point_links_checked18645 : (cuts18645.take 2).map (fun c => (2447769601-1+2*2^9*c.k,99110258188717+c.lower,99110638016781+c.upper)) = pointBounds18645 := by
 decide +kernel
def cuts18646 : List PrefixCut := [⟨64,339319811,339320020⟩,
⟨128,687944120,687944535⟩]
theorem checked18646 : checkPrefixCuts (2^48) 2447900673 9 Manual.Count131072.C018646.packed 128 cuts18646 = true := by
 decide +kernel
def pointBounds18646 : List (Nat × Nat × Nat) := [(2447966208,99111298368316,99111678197004)]
theorem point_links_checked18646 : (cuts18646.take 1).map (fun c => (2447900673-1+2*2^9*c.k,99110959048505+c.lower,99111338876984+c.upper)) = pointBounds18646 := by
 decide +kernel
def cuts18647 : List PrefixCut := [⟨11,59559544,59559579⟩,
⟨86,467040696,467040976⟩,
⟨128,688942289,688942701⟩]
theorem checked18647 : checkPrefixCuts (2^48) 2448031745 9 Manual.Count131072.C018647.packed 128 cuts18647 = true := by
 decide +kernel
def pointBounds18647 : List (Nat × Nat × Nat) := [(2448043008,99111706552169,99112086381098),(2448119808,99112114033321,99112493862495)]
theorem point_links_checked18647 : (cuts18647.take 2).map (fun c => (2448031745-1+2*2^9*c.k,99111646992625+c.lower,99112026821519+c.upper)) = pointBounds18647 := by
 decide +kernel
def cuts18648 : List PrefixCut := [⟨33,181082665,181082775⟩,
⟨108,587733539,587733891⟩,
⟨128,697988083,697988498⟩]
theorem checked18648 : checkPrefixCuts (2^48) 2448162817 9 Manual.Count131072.C018648.packed 128 cuts18648 = true := by
 decide +kernel
def pointBounds18648 : List (Nat × Nat × Nat) := [(2448196608,99112517017579,99112896846995),(2448273408,99112923668453,99113303498111)]
theorem point_links_checked18648 : (cuts18648.take 2).map (fun c => (2448162817-1+2*2^9*c.k,99112335934914+c.lower,99112715764220+c.upper)) = pointBounds18648 := by
 decide +kernel
def cuts18649 : List PrefixCut := [⟨55,297073289,297073467⟩,
⟨128,684959761,684960174⟩]
theorem checked18649 : checkPrefixCuts (2^48) 2448293889 9 Manual.Count131072.C018649.packed 128 cuts18649 = true := by
 decide +kernel
def pointBounds18649 : List (Nat × Nat × Nat) := [(2448350208,99113330996286,99113710826185)]
theorem point_links_checked18649 : (cuts18649.take 1).map (fun c => (2448293889-1+2*2^9*c.k,99113033922997+c.lower,99113413752718+c.upper)) = pointBounds18649 := by
 decide +kernel
def cuts18650 : List PrefixCut := [⟨2,11496157,11496164⟩,
⟨77,417533869,417534118⟩,
⟨128,696418829,696419249⟩]
theorem checked18650 : checkPrefixCuts (2^48) 2448424961 9 Manual.Count131072.C018650.packed 128 cuts18650 = true := by
 decide +kernel
def pointBounds18650 : List (Nat × Nat × Nat) := [(2448427008,99113730378915,99114110209056),(2448503808,99114136416627,99114516247010)]
theorem point_links_checked18650 : (cuts18650.take 2).map (fun c => (2448424961-1+2*2^9*c.k,99113718882758+c.lower,99114098712892+c.upper)) = pointBounds18650 := by
 decide +kernel
def cuts18651 : List PrefixCut := [⟨24,132198131,132198212⟩,
⟨99,536830999,536831327⟩,
⟨128,692703220,692703642⟩]
theorem checked18651 : checkPrefixCuts (2^48) 2448556033 9 Manual.Count131072.C018651.packed 128 cuts18651 = true := by
 decide +kernel
def pointBounds18651 : List (Nat × Nat × Nat) := [(2448580608,99114547499718,99114927330353),(2448657408,99114952132586,99115331963468)]
theorem point_links_checked18651 : (cuts18651.take 2).map (fun c => (2448556033-1+2*2^9*c.k,99114415301587+c.lower,99114795132141+c.upper)) = pointBounds18651 := by
 decide +kernel
def cuts18652 : List PrefixCut := [⟨46,251851525,251851677⟩,
⟨121,657378467,657378861⟩,
⟨128,693585615,693586032⟩]
theorem checked18652 : checkPrefixCuts (2^48) 2448687105 9 Manual.Count131072.C018652.packed 128 cuts18652 = true := by
 decide +kernel
def pointBounds18652 : List (Nat × Nat × Nat) := [(2448734208,99115359856332,99115739687460),(2448811008,99115765383274,99116145214644)]
theorem point_links_checked18652 : (cuts18652.take 2).map (fun c => (2448687105-1+2*2^9*c.k,99115108004807+c.lower,99115487835783+c.upper)) = pointBounds18652 := by
 decide +kernel
def cuts18653 : List PrefixCut := [⟨68,372180720,372180942⟩,
⟨128,699410562,699410980⟩]
theorem checked18653 : checkPrefixCuts (2^48) 2448818177 9 Manual.Count131072.C018653.packed 128 cuts18653 = true := by
 decide +kernel
def pointBounds18653 : List (Nat × Nat × Nat) := [(2448887808,99116173771142,99116553602757)]
theorem point_links_checked18653 : (cuts18653.take 1).map (fun c => (2448818177-1+2*2^9*c.k,99115801590422+c.lower,99116181421815+c.upper)) = pointBounds18653 := by
 decide +kernel
def cuts18654 : List PrefixCut := [⟨15,82409578,82409629⟩,
⟨90,490426910,490427210⟩,
⟨128,697304056,697304482⟩]
theorem checked18654 : checkPrefixCuts (2^48) 2448949249 9 Manual.Count131072.C018654.packed 128 cuts18654 = true := by
 decide +kernel
def pointBounds18654 : List (Nat × Nat × Nat) := [(2448964608,99116583410562,99116963242424),(2449041408,99116991427894,99117371260005)]
theorem point_links_checked18654 : (cuts18654.take 2).map (fun c => (2448949249-1+2*2^9*c.k,99116501000984+c.lower,99116880832795+c.upper)) = pointBounds18654 := by
 decide +kernel
def cuts18655 : List PrefixCut := [⟨37,202506603,202506724⟩,
⟨112,607510331,607510693⟩,
⟨128,694278772,694279186⟩]
theorem checked18655 : checkPrefixCuts (2^48) 2449080321 9 Manual.Count131072.C018655.packed 128 cuts18655 = true := by
 decide +kernel
def pointBounds18655 : List (Nat × Nat × Nat) := [(2449118208,99117400811643,99117780644001),(2449195008,99117805815371,99118185647970)]
theorem point_links_checked18655 : (cuts18655.take 2).map (fun c => (2449080321-1+2*2^9*c.k,99117198305040+c.lower,99117578137277+c.upper)) = pointBounds18655 := by
 decide +kernel
def cuts18656 : List PrefixCut := [⟨59,312016653,312016840⟩,
⟨128,689989168,689989579⟩]
theorem checked18656 : checkPrefixCuts (2^48) 2449211393 9 Manual.Count131072.C018656.packed 128 cuts18656 = true := by
 decide +kernel
def pointBounds18656 : List (Nat × Nat × Nat) := [(2449271808,99118204600465,99118584433303)]
theorem point_links_checked18656 : (cuts18656.take 1).map (fun c => (2449211393-1+2*2^9*c.k,99117892583812+c.lower,99118272416463+c.upper)) = pointBounds18656 := by
 decide +kernel
def cuts18657 : List PrefixCut := [⟨6,30913054,30913072⟩,
⟨81,439555957,439556226⟩,
⟨128,695353482,695353908⟩]
theorem checked18657 : checkPrefixCuts (2^48) 2449342465 9 Manual.Count131072.C018657.packed 128 cuts18657 = true := by
 decide +kernel
def pointBounds18657 : List (Nat × Nat × Nat) := [(2449348608,99118613486034,99118993319114),(2449425408,99119022128937,99119401962268)]
theorem point_links_checked18657 : (cuts18657.take 2).map (fun c => (2449342465-1+2*2^9*c.k,99118582572980+c.lower,99118962406042+c.upper)) = pointBounds18657 := by
 decide +kernel
def cuts18658 : List PrefixCut := [⟨28,149385247,149385337⟩,
⟨103,553980714,553981049⟩,
⟨128,690949681,690950102⟩]
theorem checked18658 : checkPrefixCuts (2^48) 2449473537 9 Manual.Count131072.C018658.packed 128 cuts18658 = true := by
 decide +kernel
def pointBounds18658 : List (Nat × Nat × Nat) := [(2449502208,99119427311709,99119807145287),(2449579008,99119831907176,99120211740999)]
theorem point_links_checked18658 : (cuts18658.take 2).map (fun c => (2449473537-1+2*2^9*c.k,99119277926462+c.lower,99119657759950+c.upper)) = pointBounds18658 := by
 decide +kernel
def cuts18659 : List PrefixCut := [⟨50,269452328,269452494⟩,
⟨125,675745980,675746394⟩,
⟨128,692176706,692177129⟩]
theorem checked18659 : checkPrefixCuts (2^48) 2449604609 9 Manual.Count131072.C018659.packed 128 cuts18659 = true := by
 decide +kernel
def pointBounds18659 : List (Nat × Nat × Nat) := [(2449655808,99120238328471,99120618162546),(2449732608,99120644622123,99121024456446)]
theorem point_links_checked18659 : (cuts18659.take 2).map (fun c => (2449604609-1+2*2^9*c.k,99119968876143+c.lower,99120348710052+c.upper)) = pointBounds18659 := by
 decide +kernel
def cuts18660 : List PrefixCut := [⟨72,385024547,385024774⟩,
⟨128,687084318,687084728⟩]
theorem checked18660 : checkPrefixCuts (2^48) 2449735681 9 Manual.Count131072.C018660.packed 128 cuts18660 = true := by
 decide +kernel
def pointBounds18660 : List (Nat × Nat × Nat) := [(2449809408,99121046077396,99121425911955)]
theorem point_links_checked18660 : (cuts18660.take 1).map (fun c => (2449735681-1+2*2^9*c.k,99120661052849+c.lower,99121040887181+c.upper)) = pointBounds18660 := by
 decide +kernel
def cuts18661 : List PrefixCut := [⟨19,106391380,106391442⟩,
⟨94,516208436,516208748⟩,
⟨128,694745397,694745819⟩]
theorem checked18661 : checkPrefixCuts (2^48) 2449866753 9 Manual.Count131072.C018661.packed 128 cuts18661 = true := by
 decide +kernel
def pointBounds18661 : List (Nat × Nat × Nat) := [(2449886208,99121454528547,99121834363351),(2449963008,99121864345603,99122244180657)]
theorem point_links_checked18661 : (cuts18661.take 2).map (fun c => (2449866753-1+2*2^9*c.k,99121348137167+c.lower,99121727971909+c.upper)) = pointBounds18661 := by
 decide +kernel
def cuts18662 : List PrefixCut := [⟨41,222306014,222306148⟩,
⟨116,631178332,631178711⟩,
⟨128,696661046,696661462⟩]
theorem checked18662 : checkPrefixCuts (2^48) 2449997825 9 Manual.Count131072.C018662.packed 128 cuts18662 = true := by
 decide +kernel
def pointBounds18662 : List (Nat × Nat × Nat) := [(2450039808,99122265188578,99122645023876),(2450116608,99122674060896,99123053896439)]
theorem point_links_checked18662 : (cuts18662.take 2).map (fun c => (2449997825-1+2*2^9*c.k,99122042882564+c.lower,99122422717728+c.upper)) = pointBounds18662 := by
 decide +kernel
def cuts18663 : List PrefixCut := [⟨63,340964232,340964439⟩,
⟨128,697083204,697083622⟩]
theorem checked18663 : checkPrefixCuts (2^48) 2450128897 9 Manual.Count131072.C018663.packed 128 cuts18663 = true := by
 decide +kernel
def pointBounds18663 : List (Nat × Nat × Nat) := [(2450193408,99123080507842,99123460343629)]
theorem point_links_checked18663 : (cuts18663.take 1).map (fun c => (2450128897-1+2*2^9*c.k,99122739543610+c.lower,99123119379190+c.upper)) = pointBounds18663 := by
 decide +kernel
def cuts18664 : List PrefixCut := [⟨10,53531882,53531914⟩,
⟨85,464892995,464893279⟩,
⟨128,698079942,698080368⟩]
theorem checked18664 : checkPrefixCuts (2^48) 2450259969 9 Manual.Count131072.C018664.packed 128 cuts18664 = true := by
 decide +kernel
def pointBounds18664 : List (Nat × Nat × Nat) := [(2450270208,99123490158696,99123869994726),(2450347008,99123901519809,99124281356091)]
theorem point_links_checked18664 : (cuts18664.take 2).map (fun c => (2450259969-1+2*2^9*c.k,99123436626814+c.lower,99123816462812+c.upper)) = pointBounds18664 := by
 decide +kernel
def cuts18665 : List PrefixCut := [⟨32,172417773,172417875⟩,
⟨107,576401668,576402015⟩,
⟨128,691035672,691036091⟩]
theorem checked18665 : checkPrefixCuts (2^48) 2450391041 9 Manual.Count131072.C018665.packed 128 cuts18665 = true := by
 decide +kernel
def pointBounds18665 : List (Nat × Nat × Nat) := [(2450423808,99124307124529,99124686961055),(2450500608,99124711108424,99125090945195)]
theorem point_links_checked18665 : (cuts18665.take 2).map (fun c => (2450391041-1+2*2^9*c.k,99124134706756+c.lower,99124514543180+c.upper)) = pointBounds18665 := by
 decide +kernel
def cuts18666 : List PrefixCut := [⟨54,295654638,295654813⟩,
⟨128,698924030,698924446⟩]
theorem checked18666 : checkPrefixCuts (2^48) 2450522113 9 Manual.Count131072.C018666.packed 128 cuts18666 = true := by
 decide +kernel
def pointBounds18666 : List (Nat × Nat × Nat) := [(2450577408,99125121397066,99125501234084)]
theorem point_links_checked18666 : (cuts18666.take 1).map (fun c => (2450522113-1+2*2^9*c.k,99124825742428+c.lower,99125205579271+c.upper)) = pointBounds18666 := by
 decide +kernel
def cuts18667 : List PrefixCut := [⟨1,4709140,4709143⟩,
⟨76,405898460,405898708⟩,
⟨128,690272471,690272892⟩]
theorem checked18667 : checkPrefixCuts (2^48) 2450653185 9 Manual.Count131072.C018667.packed 128 cuts18667 = true := by
 decide +kernel
def pointBounds18667 : List (Nat × Nat × Nat) := [(2450654208,99125529375598,99125909212860),(2450731008,99125930564918,99126310402425)]
theorem point_links_checked18667 : (cuts18667.take 2).map (fun c => (2450653185-1+2*2^9*c.k,99125524666458+c.lower,99125904503717+c.upper)) = pointBounds18667 := by
 decide +kernel
def cuts18668 : List PrefixCut := [⟨23,127024536,127024609⟩,
⟨98,529566951,529567269⟩,
⟨128,691154588,691155002⟩]
theorem checked18668 : checkPrefixCuts (2^48) 2450784257 9 Manual.Count131072.C018668.packed 128 cuts18668 = true := by
 decide +kernel
def pointBounds18668 : List (Nat × Nat × Nat) := [(2450807808,99126341963465,99126721801218),(2450884608,99126744505880,99127124343878)]
theorem point_links_checked18668 : (cuts18668.take 2).map (fun c => (2450784257-1+2*2^9*c.k,99126214938929+c.lower,99126594776609+c.upper)) = pointBounds18668 := by
 decide +kernel
def cuts18669 : List PrefixCut := [⟨45,247028890,247029039⟩,
⟨120,649890615,649891009⟩,
⟨128,692610671,692611091⟩]
theorem checked18669 : checkPrefixCuts (2^48) 2450915329 9 Manual.Count131072.C018669.packed 128 cuts18669 = true := by
 decide +kernel
def pointBounds18669 : List (Nat × Nat × Nat) := [(2450961408,99127153122407,99127532960650),(2451038208,99127555984132,99127935822620)]
theorem point_links_checked18669 : (cuts18669.take 2).map (fun c => (2450915329-1+2*2^9*c.k,99126906093517+c.lower,99127285931611+c.upper)) = pointBounds18669 := by
 decide +kernel
def cuts18670 : List PrefixCut := [⟨67,368397249,368397475⟩,
⟨128,706583306,706583733⟩]
theorem checked18670 : checkPrefixCuts (2^48) 2451046401 9 Manual.Count131072.C018670.packed 128 cuts18670 = true := by
 decide +kernel
def pointBounds18670 : List (Nat × Nat × Nat) := [(2451115008,99127967101437,99128346940177)]
theorem point_links_checked18670 : (cuts18670.take 1).map (fun c => (2451046401-1+2*2^9*c.k,99127598704188+c.lower,99127978542702+c.upper)) = pointBounds18670 := by
 decide +kernel
def cuts18671 : List PrefixCut := [⟨14,76018906,76018953⟩,
⟨89,482287698,482287990⟩,
⟨128,696555488,696555908⟩]
theorem checked18671 : checkPrefixCuts (2^48) 2451177473 9 Manual.Count131072.C018671.packed 128 cuts18671 = true := by
 decide +kernel
def pointBounds18671 : List (Nat × Nat × Nat) := [(2451191808,99128381306400,99128761145388),(2451268608,99128787575192,99129167414425)]
theorem point_links_checked18671 : (cuts18671.take 2).map (fun c => (2451177473-1+2*2^9*c.k,99128305287494+c.lower,99128685126435+c.upper)) = pointBounds18671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000270
