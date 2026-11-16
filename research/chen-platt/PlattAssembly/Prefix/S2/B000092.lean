import PlattAssemblyKernel
import PlattCertificates.Count131072.C012944
import PlattCertificates.Count131072.C012945
import PlattCertificates.Count131072.C012946
import PlattCertificates.Count131072.C012947
import PlattCertificates.Count131072.C012948
import PlattCertificates.Count131072.C012949
import PlattCertificates.Count131072.C012950
import PlattCertificates.Count131072.C012951
import PlattCertificates.Count131072.C012952
import PlattCertificates.Count131072.C012953
import PlattCertificates.Count131072.C012954
import PlattCertificates.Count131072.C012955
import PlattCertificates.Count131072.C012956
import PlattCertificates.Count131072.C012957
import PlattCertificates.Count131072.C012958
import PlattCertificates.Count131072.C012959
import PlattCertificates.Count131072.C012960
import PlattCertificates.Count131072.C012961
import PlattCertificates.Count131072.C012962
import PlattCertificates.Count131072.C012963
import PlattCertificates.Count131072.C012964
import PlattCertificates.Count131072.C012965
import PlattCertificates.Count131072.C012966
import PlattCertificates.Count131072.C012967
import PlattCertificates.Count131072.C012968
import PlattCertificates.Count131072.C012969
import PlattCertificates.Count131072.C012970
import PlattCertificates.Count131072.C012971
import PlattCertificates.Count131072.C012972
import PlattCertificates.Count131072.C012973
import PlattCertificates.Count131072.C012974
import PlattCertificates.Count131072.C012975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12944 : List PrefixCut := [⟨46,366626275,366626540⟩,
⟨98,776440970,776441532⟩,
⟨128,1017755679,1017756418⟩]
theorem checked12944 : checkPrefixCuts (2^48) 1700528129 9 Manual.Count131072.C012944.packed 128 cuts12944 = true := by
 decide +kernel
def pointBounds12944 : List (Nat × Nat × Nat) := [(1700575232,94327827476327,94328204160123),(1700628480,94328237291022,94328613975115)]
theorem point_links_checked12944 : (cuts12944.take 2).map (fun c => (1700528129-1+2*2^9*c.k,94327460850052+c.lower,94327837533583+c.upper)) = pointBounds12944 := by
 decide +kernel
def cuts12945 : List PrefixCut := [⟨22,180900458,180900588⟩,
⟨74,599130271,599130705⟩,
⟨126,1016023036,1016023769⟩,
⟨128,1032407201,1032407945⟩]
theorem checked12945 : checkPrefixCuts (2^48) 1700659201 9 Manual.Count131072.C012945.packed 128 cuts12945 = true := by
 decide +kernel
def pointBounds12945 : List (Nat × Nat × Nat) := [(1700681728,94328659506189,94329036190589),(1700734976,94329077736002,94329454420706),(1700788224,94329494628767,94329871313770)]
theorem point_links_checked12945 : (cuts12945.take 3).map (fun c => (1700659201-1+2*2^9*c.k,94328478605731+c.lower,94328855290001+c.upper)) = pointBounds12945 := by
 decide +kernel
def cuts12946 : List PrefixCut := [⟨50,405791392,405791688⟩,
⟨102,820341230,820341825⟩,
⟨128,1035968268,1035969016⟩]
theorem checked12946 : checkPrefixCuts (2^48) 1700790273 9 Manual.Count131072.C012946.packed 128 cuts12946 = true := by
 decide +kernel
def pointBounds12946 : List (Nat × Nat × Nat) := [(1700841472,94329916804324,94330293489634),(1700894720,94330331354162,94330708039771)]
theorem point_links_checked12946 : (cuts12946.take 2).map (fun c => (1700790273-1+2*2^9*c.k,94329511012932+c.lower,94329887697946+c.upper)) = pointBounds12946 := by
 decide +kernel
def cuts12947 : List PrefixCut := [⟨26,211817601,211817759⟩,
⟨78,620880647,620881100⟩,
⟨128,1020664694,1020665434⟩]
theorem checked12947 : checkPrefixCuts (2^48) 1700921345 9 Manual.Count131072.C012947.packed 128 cuts12947 = true := by
 decide +kernel
def pointBounds12947 : List (Nat × Nat × Nat) := [(1700947968,94330758798801,94331135484721),(1701001216,94331167861847,94331544548062)]
theorem point_links_checked12947 : (cuts12947.take 2).map (fun c => (1700921345-1+2*2^9*c.k,94330546981200+c.lower,94330923666962+c.upper)) = pointBounds12947 := by
 decide +kernel
def cuts12948 : List PrefixCut := [⟨2,16712562,16712574⟩,
⟨54,429390275,429390590⟩,
⟨106,839573104,839573717⟩,
⟨128,1014298196,1014298939⟩]
theorem checked12948 : checkPrefixCuts (2^48) 1701052417 9 Manual.Count131072.C012948.packed 128 cuts12948 = true := by
 decide +kernel
def pointBounds12948 : List (Nat × Nat × Nat) := [(1701054464,94331584358456,94331961044970),(1701107712,94331997036169,94332373722986),(1701160960,94332407218998,94332783906113)]
theorem point_links_checked12948 : (cuts12948.take 3).map (fun c => (1701052417-1+2*2^9*c.k,94331567645894+c.lower,94331944332396+c.upper)) = pointBounds12948 := by
 decide +kernel
def cuts12949 : List PrefixCut := [⟨30,238754161,238754333⟩,
⟨82,653213231,653213702⟩,
⟨128,1020838371,1020839104⟩]
theorem checked12949 : checkPrefixCuts (2^48) 1701183489 9 Manual.Count131072.C012949.packed 128 cuts12949 = true := by
 decide +kernel
def pointBounds12949 : List (Nat × Nat × Nat) := [(1701214208,94332820698251,94333197385668),(1701267456,94333235157321,94333611845037)]
theorem point_links_checked12949 : (cuts12949.take 2).map (fun c => (1701183489-1+2*2^9*c.k,94332581944090+c.lower,94332958631335+c.upper)) = pointBounds12949 := by
 decide +kernel
def cuts12950 : List PrefixCut := [⟨6,48640899,48640932⟩,
⟨58,466051918,466052251⟩,
⟨110,878155830,878156465⟩,
⟨128,1019436191,1019436928⟩]
theorem checked12950 : checkPrefixCuts (2^48) 1701314561 9 Manual.Count131072.C012950.packed 128 cuts12950 = true := by
 decide +kernel
def pointBounds12950 : List (Nat × Nat × Nat) := [(1701320704,94333651423360,94334028111371),(1701373952,94334068834379,94334445522690),(1701427200,94334480938291,94334857626904)]
theorem point_links_checked12950 : (cuts12950.take 3).map (fun c => (1701314561-1+2*2^9*c.k,94333602782461+c.lower,94333979470439+c.upper)) = pointBounds12950 := by
 decide +kernel
def cuts12951 : List PrefixCut := [⟨34,273788419,273788620⟩,
⟨86,687024669,687025170⟩,
⟨128,1020681073,1020681815⟩]
theorem checked12951 : checkPrefixCuts (2^48) 1701445633 9 Manual.Count131072.C012951.packed 128 cuts12951 = true := by
 decide +kernel
def pointBounds12951 : List (Nat × Nat × Nat) := [(1701480448,94334896007071,94335272695987),(1701533696,94335309243321,94335685932537)]
theorem point_links_checked12951 : (cuts12951.take 2).map (fun c => (1701445633-1+2*2^9*c.k,94334622218652+c.lower,94334998907367+c.upper)) = pointBounds12951 := by
 decide +kernel
def cuts12952 : List PrefixCut := [⟨10,74604220,74604277⟩,
⟨62,492611591,492611945⟩,
⟨114,900350399,900351051⟩,
⟨128,1011008348,1011009081⟩]
theorem checked12952 : checkPrefixCuts (2^48) 1701576705 9 Manual.Count131072.C012952.packed 128 cuts12952 = true := by
 decide +kernel
def pointBounds12952 : List (Nat × Nat × Nat) := [(1701586944,94335717503945,94336094193459),(1701640192,94336135511316,94336512201127),(1701693440,94336543250124,94336919940233)]
theorem point_links_checked12952 : (cuts12952.take 3).map (fun c => (1701576705-1+2*2^9*c.k,94335642899725+c.lower,94336019589182+c.upper)) = pointBounds12952 := by
 decide +kernel
def cuts12953 : List PrefixCut := [⟨38,301534028,301534243⟩,
⟨90,724298745,724299269⟩,
⟨128,1023335549,1023336292⟩]
theorem checked12953 : checkPrefixCuts (2^48) 1701707777 9 Manual.Count131072.C012953.packed 128 cuts12953 = true := by
 decide +kernel
def pointBounds12953 : List (Nat × Nat × Nat) := [(1701746688,94336955442101,94337332132506),(1701799936,94337378206818,94337754897532)]
theorem point_links_checked12953 : (cuts12953.take 2).map (fun c => (1701707777-1+2*2^9*c.k,94336653908073+c.lower,94337030598263+c.upper)) = pointBounds12953 := by
 decide +kernel
def cuts12954 : List PrefixCut := [⟨14,108994554,108994632⟩,
⟨66,523794046,523794424⟩,
⟨118,933122915,933123588⟩,
⟨128,1012671797,1012672530⟩]
theorem checked12954 : checkPrefixCuts (2^48) 1701838849 9 Manual.Count131072.C012954.packed 128 cuts12954 = true := by
 decide +kernel
def pointBounds12954 : List (Nat × Nat × Nat) := [(1701853184,94337786238176,94338162929187),(1701906432,94338201037668,94338577728979),(1701959680,94338610366537,94338987058143)]
theorem point_links_checked12954 : (cuts12954.take 3).map (fun c => (1701838849-1+2*2^9*c.k,94337677243622+c.lower,94338053934555+c.upper)) = pointBounds12954 := by
 decide +kernel
def cuts12955 : List PrefixCut := [⟨42,333240225,333240466⟩,
⟨94,741551130,741551665⟩,
⟨128,1017554997,1017555732⟩]
theorem checked12955 : checkPrefixCuts (2^48) 1701969921 9 Manual.Count131072.C012955.packed 128 cuts12955 = true := by
 decide +kernel
def pointBounds12955 : List (Nat × Nat × Nat) := [(1702012928,94339023155644,94339399847551),(1702066176,94339431466549,94339808158750)]
theorem point_links_checked12955 : (cuts12955.take 2).map (fun c => (1701969921-1+2*2^9*c.k,94338689915419+c.lower,94339066607085+c.upper)) = pointBounds12955 := by
 decide +kernel
def cuts12956 : List PrefixCut := [⟨18,144697169,144697273⟩,
⟨70,555793834,555794241⟩,
⟨122,964893228,964893934⟩,
⟨128,1013673438,1013674179⟩]
theorem checked12956 : checkPrefixCuts (2^48) 1702100993 9 Manual.Count131072.C012956.packed 128 cuts12956 = true := by
 decide +kernel
def pointBounds12956 : List (Nat × Nat × Nat) := [(1702119424,94339852167585,94340228860090),(1702172672,94340263264250,94340639957058),(1702225920,94340672363644,94341049056751)]
theorem point_links_checked12956 : (cuts12956.take 3).map (fun c => (1702100993-1+2*2^9*c.k,94339707470416+c.lower,94340084162817+c.upper)) = pointBounds12956 := by
 decide +kernel
def cuts12957 : List PrefixCut := [⟨46,368739566,368739832⟩,
⟨98,781120454,781121025⟩,
⟨128,1015745162,1015745905⟩]
theorem checked12957 : checkPrefixCuts (2^48) 1702232065 9 Manual.Count131072.C012957.packed 128 cuts12957 = true := by
 decide +kernel
def pointBounds12957 : List (Nat × Nat × Nat) := [(1702279168,94341089883420,94341466576828),(1702332416,94341502264308,94341878958021)]
theorem point_links_checked12957 : (cuts12957.take 2).map (fun c => (1702232065-1+2*2^9*c.k,94340721143854+c.lower,94341097836996+c.upper)) = pointBounds12957 := by
 decide +kernel
def cuts12958 : List PrefixCut := [⟨22,174601724,174601850⟩,
⟨74,596215782,596216214⟩,
⟨126,1009054019,1009054757⟩,
⟨128,1025091125,1025091874⟩]
theorem checked12958 : checkPrefixCuts (2^48) 1702363137 9 Manual.Count131072.C012958.packed 128 cuts12958 = true := by
 decide +kernel
def pointBounds12958 : List (Nat × Nat × Nat) := [(1702385664,94341911490740,94342288184751),(1702438912,94342333104798,94342709799115),(1702492160,94342745943035,94343122637658)]
theorem point_links_checked12958 : (cuts12958.take 3).map (fun c => (1702363137-1+2*2^9*c.k,94341736889016+c.lower,94342113582901+c.upper)) = pointBounds12958 := by
 decide +kernel
def cuts12959 : List PrefixCut := [⟨50,403566612,403566901⟩,
⟨102,818693400,818693986⟩,
⟨128,1023854861,1023855599⟩]
theorem checked12959 : checkPrefixCuts (2^48) 1702494209 9 Manual.Count131072.C012959.packed 128 cuts12959 = true := by
 decide +kernel
def pointBounds12959 : List (Nat × Nat × Nat) := [(1702545408,94343165546753,94343542241676),(1702598656,94343580673541,94343957368761)]
theorem point_links_checked12959 : (cuts12959.take 2).map (fun c => (1702494209-1+2*2^9*c.k,94342761980141+c.lower,94343138674775+c.upper)) = pointBounds12959 := by
 decide +kernel
def cuts12960 : List PrefixCut := [⟨26,206646058,206646207⟩,
⟨78,614969024,614969473⟩,
⟨128,1013691736,1013692475⟩]
theorem checked12960 : checkPrefixCuts (2^48) 1702625281 9 Manual.Count131072.C012960.packed 128 cuts12960 = true := by
 decide +kernel
def pointBounds12960 : List (Nat × Nat × Nat) := [(1702651904,94343992481060,94344369176581),(1702705152,94344400804026,94344777499847)]
theorem point_links_checked12960 : (cuts12960.take 2).map (fun c => (1702625281-1+2*2^9*c.k,94343785835002+c.lower,94344162530374+c.upper)) = pointBounds12960 := by
 decide +kernel
def cuts12961 : List PrefixCut := [⟨2,17522365,17522379⟩,
⟨54,433754453,433754765⟩,
⟨106,847493998,847494611⟩,
⟨128,1018903691,1018904429⟩]
theorem checked12961 : checkPrefixCuts (2^48) 1702756353 9 Manual.Count131072.C012961.packed 128 cuts12961 = true := by
 decide +kernel
def pointBounds12961 : List (Nat × Nat × Nat) := [(1702758400,94344817049103,94345193745228),(1702811648,94345233281191,94345609977614),(1702864896,94345647020736,94346023717460)]
theorem point_links_checked12961 : (cuts12961.take 3).map (fun c => (1702756353-1+2*2^9*c.k,94344799526738+c.lower,94345176222849+c.upper)) = pointBounds12961 := by
 decide +kernel
def cuts12962 : List PrefixCut := [⟨30,241159901,241160077⟩,
⟨82,647105118,647105589⟩,
⟨128,1011883149,1011883885⟩]
theorem checked12962 : checkPrefixCuts (2^48) 1702887425 9 Manual.Count131072.C012962.packed 128 cuts12962 = true := by
 decide +kernel
def pointBounds12962 : List (Nat × Nat × Nat) := [(1702918144,94346059590330,94346436287355),(1702971392,94346465535547,94346842232867)]
theorem point_links_checked12962 : (cuts12962.take 2).map (fun c => (1702887425-1+2*2^9*c.k,94345818430429+c.lower,94346195127278+c.upper)) = pointBounds12962 := by
 decide +kernel
def cuts12963 : List PrefixCut := [⟨6,49253348,49253383⟩,
⟨58,466577247,466577580⟩,
⟨110,881904826,881905458⟩,
⟨128,1030646191,1030646929⟩]
theorem checked12963 : checkPrefixCuts (2^48) 1703018497 9 Manual.Count131072.C012963.packed 128 cuts12963 = true := by
 decide +kernel
def pointBounds12963 : List (Nat × Nat × Nat) := [(1703024640,94346879566926,94347256264546),(1703077888,94347296890825,94347673588743),(1703131136,94347712218404,94348088916621)]
theorem point_links_checked12963 : (cuts12963.take 3).map (fun c => (1703018497-1+2*2^9*c.k,94346830313578+c.lower,94347207011163+c.upper)) = pointBounds12963 := by
 decide +kernel
def cuts12964 : List PrefixCut := [⟨34,266903900,266904095⟩,
⟨86,685180269,685180763⟩,
⟨128,1019494432,1019495167⟩]
theorem checked12964 : checkPrefixCuts (2^48) 1703149569 9 Manual.Count131072.C012964.packed 128 cuts12964 = true := by
 decide +kernel
def pointBounds12964 : List (Nat × Nat × Nat) := [(1703184384,94348127863669,94348504562187),(1703237632,94348546140038,94348922838855)]
theorem point_links_checked12964 : (cuts12964.take 2).map (fun c => (1703149569-1+2*2^9*c.k,94347860959769+c.lower,94348237658092+c.upper)) = pointBounds12964 := by
 decide +kernel
def cuts12965 : List PrefixCut := [⟨10,81800750,81800811⟩,
⟨62,492945187,492945550⟩,
⟨114,915478694,915479364⟩,
⟨128,1031644192,1031644942⟩]
theorem checked12965 : checkPrefixCuts (2^48) 1703280641 9 Manual.Count131072.C012965.packed 128 cuts12965 = true := by
 decide +kernel
def pointBounds12965 : List (Nat × Nat × Nat) := [(1703290880,94348962254951,94349338954070),(1703344128,94349373399388,94349750098809),(1703397376,94349795932895,94350172632623)]
theorem point_links_checked12965 : (cuts12965.take 3).map (fun c => (1703280641-1+2*2^9*c.k,94348880454201+c.lower,94349257153259+c.upper)) = pointBounds12965 := by
 decide +kernel
def cuts12966 : List PrefixCut := [⟨38,299249519,299249740⟩,
⟨90,704076499,704077015⟩,
⟨128,1005457884,1005458617⟩]
theorem checked12966 : checkPrefixCuts (2^48) 1703411713 9 Manual.Count131072.C012966.packed 128 cuts12966 = true := by
 decide +kernel
def pointBounds12966 : List (Nat × Nat × Nat) := [(1703450624,94350211347912,94350588047941),(1703503872,94350616174892,94350992875216)]
theorem point_links_checked12966 : (cuts12966.take 2).map (fun c => (1703411713-1+2*2^9*c.k,94349912098393+c.lower,94350288798201+c.upper)) = pointBounds12966 := by
 decide +kernel
def cuts12967 : List PrefixCut := [⟨14,114007612,114007696⟩,
⟨66,519139627,519140007⟩,
⟨118,931363535,931364213⟩,
⟨128,1013476336,1013477072⟩]
theorem checked12967 : checkPrefixCuts (2^48) 1703542785 9 Manual.Count131072.C012967.packed 128 cuts12967 = true := by
 decide +kernel
def pointBounds12967 : List (Nat × Nat × Nat) := [(1703557120,94351031563889,94351408264514),(1703610368,94351436695904,94351813396825),(1703663616,94351848919812,94352225621031)]
theorem point_links_checked12967 : (cuts12967.take 3).map (fun c => (1703542785-1+2*2^9*c.k,94350917556277+c.lower,94351294256818+c.upper)) = pointBounds12967 := by
 decide +kernel
def cuts12968 : List PrefixCut := [⟨42,327124448,327124691⟩,
⟨94,746757001,746757548⟩,
⟨128,1016702623,1016703363⟩]
theorem checked12968 : checkPrefixCuts (2^48) 1703673857 9 Manual.Count131072.C012968.packed 128 cuts12968 = true := by
 decide +kernel
def pointBounds12968 : List (Nat × Nat × Nat) := [(1703716864,94352258157061,94352634858581),(1703770112,94352677789614,94353054491438)]
theorem point_links_checked12968 : (cuts12968.take 2).map (fun c => (1703673857-1+2*2^9*c.k,94351931032613+c.lower,94352307733890+c.upper)) = pointBounds12968 := by
 decide +kernel
def cuts12969 : List PrefixCut := [⟨18,149673722,149673831⟩,
⟨70,559698448,559698862⟩,
⟨122,975987754,975988469⟩,
⟨128,1019433064,1019433810⟩]
theorem checked12969 : checkPrefixCuts (2^48) 1703804929 9 Manual.Count131072.C012969.packed 128 cuts12969 = true := by
 decide +kernel
def pointBounds12969 : List (Nat × Nat × Nat) := [(1703823360,94353097408958,94353474111084),(1703876608,94353507433684,94353884136115),(1703929856,94353923722990,94354300425722)]
theorem point_links_checked12969 : (cuts12969.take 3).map (fun c => (1703804929-1+2*2^9*c.k,94352947735236+c.lower,94353324437253+c.upper)) = pointBounds12969 := by
 decide +kernel
def cuts12970 : List PrefixCut := [⟨46,365067074,365067343⟩,
⟨99,787937579,787938153⟩,
⟨128,1019519584,1019520323⟩]
theorem checked12970 : checkPrefixCuts (2^48) 1703936001 9 Manual.Count131072.C012970.packed 128 cuts12970 = true := by
 decide +kernel
def pointBounds12970 : List (Nat × Nat × Nat) := [(1703983104,94354332235374,94354708938406),(1704037376,94354755105879,94355131809216)]
theorem point_links_checked12970 : (cuts12970.take 2).map (fun c => (1703936001-1+2*2^9*c.k,94353967168300+c.lower,94354343871063+c.upper)) = pointBounds12970 := by
 decide +kernel
def cuts12971 : List PrefixCut := [⟨24,193752732,193752873⟩,
⟨77,618908643,618909089⟩,
⟨128,1031333399,1031334144⟩]
theorem checked12971 : checkPrefixCuts (2^48) 1704067073 9 Manual.Count131072.C012971.packed 128 cuts12971 = true := by
 decide +kernel
def pointBounds12971 : List (Nat × Nat × Nat) := [(1704091648,94355180440616,94355557144259),(1704145920,94355605596527,94355982300475)]
theorem point_links_checked12971 : (cuts12971.take 2).map (fun c => (1704067073-1+2*2^9*c.k,94354986687884+c.lower,94355363391386+c.upper)) = pointBounds12971 := by
 decide +kernel
def cuts12972 : List PrefixCut := [⟨2,14534562,14534573⟩,
⟨55,442140995,442141315⟩,
⟨108,859328903,859329525⟩,
⟨128,1012922028,1012922761⟩]
theorem checked12972 : checkPrefixCuts (2^48) 1704198145 9 Manual.Count131072.C012972.packed 128 cuts12972 = true := by
 decide +kernel
def pointBounds12972 : List (Nat × Nat × Nat) := [(1704200192,94356032555845,94356409260103),(1704254464,94356460162278,94356836866845),(1704308736,94356877350186,94357254055055)]
theorem point_links_checked12972 : (cuts12972.take 3).map (fun c => (1704198145-1+2*2^9*c.k,94356018021283+c.lower,94356394725530+c.upper)) = pointBounds12972 := by
 decide +kernel
def cuts12973 : List PrefixCut := [⟨33,268040513,268040709⟩,
⟨86,690156242,690156746⟩,
⟨128,1024404138,1024404885⟩]
theorem checked12973 : checkPrefixCuts (2^48) 1704329217 9 Manual.Count131072.C012973.packed 128 cuts12973 = true := by
 decide +kernel
def pointBounds12973 : List (Nat × Nat × Nat) := [(1704363008,94357298983824,94357675689000),(1704417280,94357721099553,94358097805037)]
theorem point_links_checked12973 : (cuts12973.take 2).map (fun c => (1704329217-1+2*2^9*c.k,94357030943311+c.lower,94357407648291+c.upper)) = pointBounds12973 := by
 decide +kernel
def cuts12974 : List PrefixCut := [⟨11,87193724,87193789⟩,
⟨64,510108178,510108553⟩,
⟨117,924752568,924753248⟩,
⟨128,1014086821,1014087566⟩]
theorem checked12974 : checkPrefixCuts (2^48) 1704460289 9 Manual.Count131072.C012974.packed 128 cuts12974 = true := by
 decide +kernel
def pointBounds12974 : List (Nat × Nat × Nat) := [(1704471552,94358142541173,94358519246965),(1704525824,94358565455627,94358942161729),(1704580096,94358980100017,94359356806424)]
theorem point_links_checked12974 : (cuts12974.take 3).map (fun c => (1704460289-1+2*2^9*c.k,94358055347449+c.lower,94358432053176+c.upper)) = pointBounds12974 := by
 decide +kernel
def cuts12975 : List PrefixCut := [⟨42,337681435,337681680⟩,
⟨95,759399560,759400111⟩,
⟨128,1030355569,1030356313⟩]
theorem checked12975 : checkPrefixCuts (2^48) 1704591361 9 Manual.Count131072.C012975.packed 128 cuts12975 = true := by
 decide +kernel
def pointBounds12975 : List (Nat × Nat × Nat) := [(1704634368,94359407115705,94359783822422),(1704688640,94359828833830,94360205540853)]
theorem point_links_checked12975 : (cuts12975.take 2).map (fun c => (1704591361-1+2*2^9*c.k,94359069434270+c.lower,94359446140742+c.upper)) = pointBounds12975 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000092
