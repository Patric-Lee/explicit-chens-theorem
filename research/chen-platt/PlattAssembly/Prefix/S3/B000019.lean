import PlattAssemblyKernel
import PlattCertificates.Count131072.C020608
import PlattCertificates.Count131072.C020609
import PlattCertificates.Count131072.C020610
import PlattCertificates.Count131072.C020611
import PlattCertificates.Count131072.C020612
import PlattCertificates.Count131072.C020613
import PlattCertificates.Count131072.C020614
import PlattCertificates.Count131072.C020615
import PlattCertificates.Count131072.C020616
import PlattCertificates.Count131072.C020617
import PlattCertificates.Count131072.C020618
import PlattCertificates.Count131072.C020619
import PlattCertificates.Count131072.C020620
import PlattCertificates.Count131072.C020621
import PlattCertificates.Count131072.C020622
import PlattCertificates.Count131072.C020623
import PlattCertificates.Count131072.C020624
import PlattCertificates.Count131072.C020625
import PlattCertificates.Count131072.C020626
import PlattCertificates.Count131072.C020627
import PlattCertificates.Count131072.C020628
import PlattCertificates.Count131072.C020629
import PlattCertificates.Count131072.C020630
import PlattCertificates.Count131072.C020631
import PlattCertificates.Count131072.C020632
import PlattCertificates.Count131072.C020633
import PlattCertificates.Count131072.C020634
import PlattCertificates.Count131072.C020635
import PlattCertificates.Count131072.C020636
import PlattCertificates.Count131072.C020637
import PlattCertificates.Count131072.C020638
import PlattCertificates.Count131072.C020639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20608 : List PrefixCut := [⟨34,166590670,166590767⟩,
⟨117,578531871,578532205⟩,
⟨128,635135061,635135426⟩]
theorem checked20608 : checkPrefixCuts (2^48) 2705063937 9 Manual.Count131072.C020608.packed 128 cuts20608 = true := by
 decide +kernel
def pointBounds20608 : List (Nat × Nat × Nat) := [(2705098752,100408820216127,100409200812922),(2705183744,100409232157328,100409612754360)]
theorem point_links_checked20608 : (cuts20608.take 2).map (fun c => (2705063937-1+2*2^9*c.k,100408653625457+c.lower,100409034222155+c.upper)) = pointBounds20608 := by
 decide +kernel
def cuts20609 : List PrefixCut := [⟨72,348770010,348770212⟩,
⟨128,621786234,621786596⟩]
theorem checked20609 : checkPrefixCuts (2^48) 2705195009 9 Manual.Count131072.C020609.packed 128 cuts20609 = true := by
 decide +kernel
def pointBounds20609 : List (Nat × Nat × Nat) := [(2705268736,100409637530528,100410018127793)]
theorem point_links_checked20609 : (cuts20609.take 1).map (fun c => (2705195009-1+2*2^9*c.k,100409288760518+c.lower,100409669357581+c.upper)) = pointBounds20609 := by
 decide +kernel
def cuts20610 : List PrefixCut := [⟨27,129535003,129535080⟩,
⟨110,541541370,541541690⟩,
⟨128,630495597,630495972⟩]
theorem checked20610 : checkPrefixCuts (2^48) 2705326081 9 Manual.Count131072.C020610.packed 128 cuts20610 = true := by
 decide +kernel
def pointBounds20610 : List (Nat × Nat × Nat) := [(2705353728,100410040081755,100410420679257),(2705438720,100410452088122,100410832685867)]
theorem point_links_checked20610 : (cuts20610.take 2).map (fun c => (2705326081-1+2*2^9*c.k,100409910546752+c.lower,100410291144177+c.upper)) = pointBounds20610 := by
 decide +kernel
def cuts20611 : List PrefixCut := [⟨65,321270587,321270771⟩,
⟨128,633378234,633378598⟩]
theorem checked20611 : checkPrefixCuts (2^48) 2705457153 9 Manual.Count131072.C020611.packed 128 cuts20611 = true := by
 decide +kernel
def pointBounds20611 : List (Nat × Nat × Nat) := [(2705523712,100410862312936,100411242910920)]
theorem point_links_checked20611 : (cuts20611.take 1).map (fun c => (2705457153-1+2*2^9*c.k,100410541042349+c.lower,100410921640149+c.upper)) = pointBounds20611 := by
 decide +kernel
def cuts20612 : List PrefixCut := [⟨20,96335710,96335765⟩,
⟨103,503413781,503414070⟩,
⟨128,628561982,628562342⟩]
theorem checked20612 : checkPrefixCuts (2^48) 2705588225 9 Manual.Count131072.C020612.packed 128 cuts20612 = true := by
 decide +kernel
def pointBounds20612 : List (Nat × Nat × Nat) := [(2705608704,100411270756293,100411651354512),(2705693696,100411677834364,100412058432817)]
theorem point_links_checked20612 : (cuts20612.take 2).map (fun c => (2705588225-1+2*2^9*c.k,100411174420583+c.lower,100411555018747+c.upper)) = pointBounds20612 := by
 decide +kernel
def cuts20613 : List PrefixCut := [⟨58,275987516,275987680⟩,
⟨128,622081834,622082197⟩]
theorem checked20613 : checkPrefixCuts (2^48) 2705719297 9 Manual.Count131072.C020613.packed 128 cuts20613 = true := by
 decide +kernel
def pointBounds20613 : List (Nat × Nat × Nat) := [(2705778688,100412078970081,100412459568769)]
theorem point_links_checked20613 : (cuts20613.take 1).map (fun c => (2705719297-1+2*2^9*c.k,100411802982565+c.lower,100412183581089+c.upper)) = pointBounds20613 := by
 decide +kernel
def cuts20614 : List PrefixCut := [⟨13,63350802,63350836⟩,
⟨96,468830198,468830466⟩,
⟨128,626004653,626005012⟩]
theorem checked20614 : checkPrefixCuts (2^48) 2705850369 9 Manual.Count131072.C020614.packed 128 cuts20614 = true := by
 decide +kernel
def pointBounds20614 : List (Nat × Nat × Nat) := [(2705863680,100412488415201,100412869014122),(2705948672,100412893894597,100413274493752)]
theorem point_links_checked20614 : (cuts20614.take 2).map (fun c => (2705850369-1+2*2^9*c.k,100412425064399+c.lower,100412805663286+c.upper)) = pointBounds20614 := by
 decide +kernel
def cuts20615 : List PrefixCut := [⟨51,246419905,246420049⟩,
⟨128,623373851,623374214⟩]
theorem checked20615 : checkPrefixCuts (2^48) 2705981441 9 Manual.Count131072.C020615.packed 128 cuts20615 = true := by
 decide +kernel
def pointBounds20615 : List (Nat × Nat × Nat) := [(2706033664,100413297488957,100413678088347)]
theorem point_links_checked20615 : (cuts20615.take 1).map (fun c => (2705981441-1+2*2^9*c.k,100413051069052+c.lower,100413431668298+c.upper)) = pointBounds20615 := by
 decide +kernel
def cuts20616 : List PrefixCut := [⟨6,32140437,32140455⟩,
⟨89,443406320,443406571⟩,
⟨128,636345272,636345632⟩]
theorem checked20616 : checkPrefixCuts (2^48) 2706112513 9 Manual.Count131072.C020616.packed 128 cuts20616 = true := by
 decide +kernel
def pointBounds20616 : List (Nat × Nat × Nat) := [(2706118656,100413706583340,100414087182967),(2706203648,100414117849223,100414498449083)]
theorem point_links_checked20616 : (cuts20616.take 2).map (fun c => (2706112513-1+2*2^9*c.k,100413674442903+c.lower,100414055042512+c.upper)) = pointBounds20616 := by
 decide +kernel
def cuts20617 : List PrefixCut := [⟨44,216233865,216233994⟩,
⟨127,621545511,621545879⟩,
⟨128,626329715,626330085⟩]
theorem checked20617 : checkPrefixCuts (2^48) 2706243585 9 Manual.Count131072.C020617.packed 128 cuts20617 = true := by
 decide +kernel
def pointBounds20617 : List (Nat × Nat × Nat) := [(2706288640,100414527022040,100414907622138),(2706373632,100414932333686,100415312934023)]
theorem point_links_checked20617 : (cuts20617.take 2).map (fun c => (2706243585-1+2*2^9*c.k,100414310788175+c.lower,100414691388144+c.upper)) = pointBounds20617 := by
 decide +kernel
def cuts20618 : List PrefixCut := [⟨82,402594875,402595104⟩,
⟨128,631187508,631187874⟩]
theorem checked20618 : checkPrefixCuts (2^48) 2706374657 9 Manual.Count131072.C020618.packed 128 cuts20618 = true := by
 decide +kernel
def pointBounds20618 : List (Nat × Nat × Nat) := [(2706458624,100415339712765,100415720313333)]
theorem point_links_checked20618 : (cuts20618.take 1).map (fun c => (2706374657-1+2*2^9*c.k,100414937117890+c.lower,100415317718229+c.upper)) = pointBounds20618 := by
 decide +kernel
def cuts20619 : List PrefixCut := [⟨37,180645656,180645759⟩,
⟨120,589247048,589247393⟩,
⟨128,630220879,630221248⟩]
theorem checked20619 : checkPrefixCuts (2^48) 2706505729 9 Manual.Count131072.C020619.packed 128 cuts20619 = true := by
 decide +kernel
def pointBounds20619 : List (Nat × Nat × Nat) := [(2706543616,100415748951054,100416129551862),(2706628608,100416157552446,100416538153496)]
theorem point_links_checked20619 : (cuts20619.take 2).map (fun c => (2706505729-1+2*2^9*c.k,100415568305398+c.lower,100415948906103+c.upper)) = pointBounds20619 := by
 decide +kernel
def cuts20620 : List PrefixCut := [⟨75,367926770,367926984⟩,
⟨128,623535040,623535401⟩]
theorem checked20620 : checkPrefixCuts (2^48) 2706636801 9 Manual.Count131072.C020620.packed 128 cuts20620 = true := by
 decide +kernel
def pointBounds20620 : List (Nat × Nat × Nat) := [(2706713600,100416566453047,100416947054335)]
theorem point_links_checked20620 : (cuts20620.take 1).map (fun c => (2706636801-1+2*2^9*c.k,100416198526277+c.lower,100416579127351+c.upper)) = pointBounds20620 := by
 decide +kernel
def cuts20621 : List PrefixCut := [⟨30,142984480,142984565⟩,
⟨113,554354951,554355274⟩,
⟨128,625168438,625168804⟩]
theorem checked20621 : checkPrefixCuts (2^48) 2706767873 9 Manual.Count131072.C020621.packed 128 cuts20621 = true := by
 decide +kernel
def pointBounds20621 : List (Nat × Nat × Nat) := [(2706798592,100416965045797,100417345647317),(2706883584,100417376416268,100417757018026)]
theorem point_links_checked20621 : (cuts20621.take 2).map (fun c => (2706767873-1+2*2^9*c.k,100416822061317+c.lower,100417202662752+c.upper)) = pointBounds20621 := by
 decide +kernel
def cuts20622 : List PrefixCut := [⟨68,335968839,335969034⟩,
⟨128,629817474,629817840⟩]
theorem checked20622 : checkPrefixCuts (2^48) 2706898945 9 Manual.Count131072.C020622.packed 128 cuts20622 = true := by
 decide +kernel
def pointBounds20622 : List (Nat × Nat × Nat) := [(2706968576,100417783198594,100418163800590)]
theorem point_links_checked20622 : (cuts20622.take 1).map (fun c => (2706898945-1+2*2^9*c.k,100417447229755+c.lower,100417827831556+c.upper)) = pointBounds20622 := by
 decide +kernel
def cuts20623 : List PrefixCut := [⟨23,111257297,111257362⟩,
⟨106,516350523,516350819⟩,
⟨128,625107987,625108347⟩]
theorem checked20623 : checkPrefixCuts (2^48) 2707030017 9 Manual.Count131072.C020623.packed 128 cuts20623 = true := by
 decide +kernel
def pointBounds20623 : List (Nat × Nat × Nat) := [(2707053568,100418188304526,100418568906758),(2707138560,100418593397752,100418974000215)]
theorem point_links_checked20623 : (cuts20623.take 2).map (fun c => (2707030017-1+2*2^9*c.k,100418077047229+c.lower,100418457649396+c.upper)) = pointBounds20623 := by
 decide +kernel
def cuts20624 : List PrefixCut := [⟨61,301417682,301417859⟩,
⟨128,632979552,632979921⟩]
theorem checked20624 : checkPrefixCuts (2^48) 2707161089 9 Manual.Count131072.C020624.packed 128 cuts20624 = true := by
 decide +kernel
def pointBounds20624 : List (Nat × Nat × Nat) := [(2707223552,100419003572898,100419384175602)]
theorem point_links_checked20624 : (cuts20624.take 1).map (fun c => (2707161089-1+2*2^9*c.k,100418702155216+c.lower,100419082757743+c.upper)) = pointBounds20624 := by
 decide +kernel
def cuts20625 : List PrefixCut := [⟨16,78080601,78080648⟩,
⟨99,491660906,491661197⟩,
⟨128,627854664,627855036⟩]
theorem checked20625 : checkPrefixCuts (2^48) 2707292161 9 Manual.Count131072.C020625.packed 128 cuts20625 = true := by
 decide +kernel
def pointBounds20625 : List (Nat × Nat × Nat) := [(2707308544,100419413215369,100419793818312),(2707393536,100419826795674,100420207398861)]
theorem point_links_checked20625 : (cuts20625.take 2).map (fun c => (2707292161-1+2*2^9*c.k,100419335134768+c.lower,100419715737664+c.upper)) = pointBounds20625 := by
 decide +kernel
def cuts20626 : List PrefixCut := [⟨54,262714680,262714833⟩,
⟨128,624393440,624393801⟩]
theorem checked20626 : checkPrefixCuts (2^48) 2707423233 9 Manual.Count131072.C020626.packed 128 cuts20626 = true := by
 decide +kernel
def pointBounds20626 : List (Nat × Nat × Nat) := [(2707478528,100420225704112,100420606307533)]
theorem point_links_checked20626 : (cuts20626.take 1).map (fun c => (2707423233-1+2*2^9*c.k,100419962989432+c.lower,100420343592700+c.upper)) = pointBounds20626 := by
 decide +kernel
def cuts20627 : List PrefixCut := [⟨9,43246911,43246938⟩,
⟨92,456996139,456996409⟩,
⟨128,636214156,636214532⟩]
theorem checked20627 : checkPrefixCuts (2^48) 2707554305 9 Manual.Count131072.C020627.packed 128 cuts20627 = true := by
 decide +kernel
def pointBounds20627 : List (Nat × Nat × Nat) := [(2707563520,100420630629783,100421011233439),(2707648512,100421044379011,100421424982910)]
theorem point_links_checked20627 : (cuts20627.take 2).map (fun c => (2707554305-1+2*2^9*c.k,100420587382872+c.lower,100420967986501+c.upper)) = pointBounds20627 := by
 decide +kernel
def cuts20628 : List PrefixCut := [⟨47,231087843,231087974⟩,
⟨128,626308089,626308452⟩]
theorem checked20628 : checkPrefixCuts (2^48) 2707685377 9 Manual.Count131072.C020628.packed 128 cuts20628 = true := by
 decide +kernel
def pointBounds20628 : List (Nat × Nat × Nat) := [(2707733504,100421454684871,100421835289007)]
theorem point_links_checked20628 : (cuts20628.take 1).map (fun c => (2707685377-1+2*2^9*c.k,100421223597028+c.lower,100421604201033+c.upper)) = pointBounds20628 := by
 decide +kernel
def cuts20629 : List PrefixCut := [⟨2,10290951,10290957⟩,
⟨85,414853951,414854188⟩,
⟨128,620872624,620872978⟩]
theorem checked20629 : checkPrefixCuts (2^48) 2707816449 9 Manual.Count131072.C020629.packed 128 cuts20629 = true := by
 decide +kernel
def pointBounds20629 : List (Nat × Nat × Nat) := [(2707818496,100421860196068,100422240800442),(2707903488,100422264759068,100422645363673)]
theorem point_links_checked20629 : (cuts20629.take 2).map (fun c => (2707816449-1+2*2^9*c.k,100421849905117+c.lower,100422230509485+c.upper)) = pointBounds20629 := by
 decide +kernel
def cuts20630 : List PrefixCut := [⟨40,196140832,196140948⟩,
⟨123,601405935,601406286⟩,
⟨128,628222213,628222580⟩]
theorem checked20630 : checkPrefixCuts (2^48) 2707947521 9 Manual.Count131072.C020630.packed 128 cuts20630 = true := by
 decide +kernel
def pointBounds20630 : List (Nat × Nat × Nat) := [(2707988480,100422666918573,100423047523411),(2708073472,100423072183676,100423452788749)]
theorem point_links_checked20630 : (cuts20630.take 2).map (fun c => (2707947521-1+2*2^9*c.k,100422470777741+c.lower,100422851382463+c.upper)) = pointBounds20630 := by
 decide +kernel
def cuts20631 : List PrefixCut := [⟨78,382074030,382074249⟩,
⟨128,628607691,628608056⟩]
theorem checked20631 : checkPrefixCuts (2^48) 2708078593 9 Manual.Count131072.C020631.packed 128 cuts20631 = true := by
 decide +kernel
def pointBounds20631 : List (Nat × Nat × Nat) := [(2708158464,100423481073984,100423861679292)]
theorem point_links_checked20631 : (cuts20631.take 1).map (fun c => (2708078593-1+2*2^9*c.k,100423098999954+c.lower,100423479605043+c.upper)) = pointBounds20631 := by
 decide +kernel
def cuts20632 : List PrefixCut := [⟨33,157978605,157978701⟩,
⟨116,567986430,567986768⟩,
⟨128,627849617,627849989⟩]
theorem checked20632 : checkPrefixCuts (2^48) 2708209665 9 Manual.Count131072.C020632.packed 128 cuts20632 = true := by
 decide +kernel
def pointBounds20632 : List (Nat × Nat × Nat) := [(2708243456,100423885586250,100424266191800),(2708328448,100424295594075,100424676199867)]
theorem point_links_checked20632 : (cuts20632.take 2).map (fun c => (2708209665-1+2*2^9*c.k,100423727607645+c.lower,100424108213099+c.upper)) = pointBounds20632 := by
 decide +kernel
def cuts20633 : List PrefixCut := [⟨71,354600656,354600861⟩,
⟨128,634678513,634678884⟩]
theorem checked20633 : checkPrefixCuts (2^48) 2708340737 9 Manual.Count131072.C020633.packed 128 cuts20633 = true := by
 decide +kernel
def pointBounds20633 : List (Nat × Nat × Nat) := [(2708413440,100424710057918,100425090663949)]
theorem point_links_checked20633 : (cuts20633.take 1).map (fun c => (2708340737-1+2*2^9*c.k,100424355457262+c.lower,100424736063088+c.upper)) = pointBounds20633 := by
 decide +kernel
def cuts20634 : List PrefixCut := [⟨26,126994369,126994442⟩,
⟨109,532598989,532599298⟩,
⟨128,625502770,625503133⟩]
theorem checked20634 : checkPrefixCuts (2^48) 2708471809 9 Manual.Count131072.C020634.packed 128 cuts20634 = true := by
 decide +kernel
def pointBounds20634 : List (Nat × Nat × Nat) := [(2708498432,100425117130144,100425497736414),(2708583424,100425522734764,100425903341270)]
theorem point_links_checked20634 : (cuts20634.take 2).map (fun c => (2708471809-1+2*2^9*c.k,100424990135775+c.lower,100425370741972+c.upper)) = pointBounds20634 := by
 decide +kernel
def cuts20635 : List PrefixCut := [⟨64,314974195,314974374⟩,
⟨128,631915212,631915575⟩]
theorem checked20635 : checkPrefixCuts (2^48) 2708602881 9 Manual.Count131072.C020635.packed 128 cuts20635 = true := by
 decide +kernel
def pointBounds20635 : List (Nat × Nat × Nat) := [(2708668416,100425930612740,100426311219479)]
theorem point_links_checked20635 : (cuts20635.take 1).map (fun c => (2708602881-1+2*2^9*c.k,100425615638545+c.lower,100425996245105+c.upper)) = pointBounds20635 := by
 decide +kernel
def cuts20636 : List PrefixCut := [⟨19,94041658,94041713⟩,
⟨102,490983420,490983705⟩,
⟨128,620973971,620974331⟩]
theorem checked20636 : checkPrefixCuts (2^48) 2708733953 9 Manual.Count131072.C020636.packed 128 cuts20636 = true := by
 decide +kernel
def pointBounds20636 : List (Nat × Nat × Nat) := [(2708753408,100426341595415,100426722202393),(2708838400,100426738537177,100427119144385)]
theorem point_links_checked20636 : (cuts20636.take 2).map (fun c => (2708733953-1+2*2^9*c.k,100426247553757+c.lower,100426628160680+c.upper)) = pointBounds20636 := by
 decide +kernel
def cuts20637 : List PrefixCut := [⟨57,280238992,280239153⟩,
⟨128,625411903,625412266⟩]
theorem checked20637 : checkPrefixCuts (2^48) 2708865025 9 Manual.Count131072.C020637.packed 128 cuts20637 = true := by
 decide +kernel
def pointBounds20637 : List (Nat × Nat × Nat) := [(2708923392,100427148766720,100427529374164)]
theorem point_links_checked20637 : (cuts20637.take 1).map (fun c => (2708865025-1+2*2^9*c.k,100426868527728+c.lower,100427249135011+c.upper)) = pointBounds20637 := by
 decide +kernel
def cuts20638 : List PrefixCut := [⟨12,58289876,58289912⟩,
⟨95,470779502,470779774⟩,
⟨128,628810478,628810842⟩]
theorem checked20638 : checkPrefixCuts (2^48) 2708996097 9 Manual.Count131072.C020638.packed 128 cuts20638 = true := by
 decide +kernel
def pointBounds20638 : List (Nat × Nat × Nat) := [(2709008384,100427552229507,100427932837189),(2709093376,100427964719133,100428345327051)]
theorem point_links_checked20638 : (cuts20638.take 2).map (fun c => (2708996097-1+2*2^9*c.k,100427493939631+c.lower,100427874547277+c.upper)) = pointBounds20638 := by
 decide +kernel
def cuts20639 : List PrefixCut := [⟨50,240107692,240107835⟩,
⟨128,620675993,620676358⟩]
theorem checked20639 : checkPrefixCuts (2^48) 2709127169 9 Manual.Count131072.C020639.packed 128 cuts20639 = true := by
 decide +kernel
def pointBounds20639 : List (Nat × Nat × Nat) := [(2709178368,100428362857801,100428743465954)]
theorem point_links_checked20639 : (cuts20639.take 1).map (fun c => (2709127169-1+2*2^9*c.k,100428122750109+c.lower,100428503358119+c.upper)) = pointBounds20639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000019
