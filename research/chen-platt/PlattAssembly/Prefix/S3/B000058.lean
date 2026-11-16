import PlattAssemblyKernel
import PlattCertificates.Count131072.C021856
import PlattCertificates.Count131072.C021857
import PlattCertificates.Count131072.C021858
import PlattCertificates.Count131072.C021859
import PlattCertificates.Count131072.C021860
import PlattCertificates.Count131072.C021861
import PlattCertificates.Count131072.C021862
import PlattCertificates.Count131072.C021863
import PlattCertificates.Count131072.C021864
import PlattCertificates.Count131072.C021865
import PlattCertificates.Count131072.C021866
import PlattCertificates.Count131072.C021867
import PlattCertificates.Count131072.C021868
import PlattCertificates.Count131072.C021869
import PlattCertificates.Count131072.C021870
import PlattCertificates.Count131072.C021871
import PlattCertificates.Count131072.C021872
import PlattCertificates.Count131072.C021873
import PlattCertificates.Count131072.C021874
import PlattCertificates.Count131072.C021875
import PlattCertificates.Count131072.C021876
import PlattCertificates.Count131072.C021877
import PlattCertificates.Count131072.C021878
import PlattCertificates.Count131072.C021879
import PlattCertificates.Count131072.C021880
import PlattCertificates.Count131072.C021881
import PlattCertificates.Count131072.C021882
import PlattCertificates.Count131072.C021883
import PlattCertificates.Count131072.C021884
import PlattCertificates.Count131072.C021885
import PlattCertificates.Count131072.C021886
import PlattCertificates.Count131072.C021887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21856 : List PrefixCut := [⟨42,195161827,195161937⟩,
⟨128,588125724,588126062⟩]
theorem checked21856 : checkPrefixCuts (2^48) 2868641793 9 Manual.Count131072.C021856.packed 128 cuts21856 = true := by
 decide +kernel
def pointBounds21856 : List (Nat × Nat × Nat) := [(2868684800,101168735814770,101169116850678)]
theorem point_links_checked21856 : (cuts21856.take 1).map (fun c => (2868641793-1+2*2^9*c.k,101168540652943+c.lower,101168921688741+c.upper)) = pointBounds21856 := by
 decide +kernel
def cuts21857 : List PrefixCut := [⟨2,8634277,8634283⟩,
⟨90,413555832,413556074⟩,
⟨128,592317744,592318088⟩]
theorem checked21857 : checkPrefixCuts (2^48) 2868772865 9 Manual.Count131072.C021857.packed 128 cuts21857 = true := by
 decide +kernel
def pointBounds21857 : List (Nat × Nat × Nat) := [(2868774912,101169137412944,101169518449086),(2868865024,101169542334499,101169923370877)]
theorem point_links_checked21857 : (cuts21857.take 2).map (fun c => (2868772865-1+2*2^9*c.k,101169128778667+c.lower,101169509814803+c.upper)) = pointBounds21857 := by
 decide +kernel
def cuts21858 : List PrefixCut := [⟨50,228011051,228011181⟩,
⟨128,590819002,590819341⟩]
theorem checked21858 : checkPrefixCuts (2^48) 2868903937 9 Manual.Count131072.C021858.packed 128 cuts21858 = true := by
 decide +kernel
def pointBounds21858 : List (Nat × Nat × Nat) := [(2868955136,101169949107462,101170330144072)]
theorem point_links_checked21858 : (cuts21858.take 1).map (fun c => (2868903937-1+2*2^9*c.k,101169721096411+c.lower,101170102132891+c.upper)) = pointBounds21858 := by
 decide +kernel
def cuts21859 : List PrefixCut := [⟨10,48170871,48170899⟩,
⟨98,456193596,456193860⟩,
⟨128,595501144,595501483⟩]
theorem checked21859 : checkPrefixCuts (2^48) 2869035009 9 Manual.Count131072.C021859.packed 128 cuts21859 = true := by
 decide +kernel
def pointBounds21859 : List (Nat × Nat × Nat) := [(2869045248,101170360086284,101170741123131),(2869135360,101170768109009,101171149146092)]
theorem point_links_checked21859 : (cuts21859.take 2).map (fun c => (2869035009-1+2*2^9*c.k,101170311915413+c.lower,101170692952232+c.upper)) = pointBounds21859 := by
 decide +kernel
def cuts21860 : List PrefixCut := [⟨58,271154963,271155125⟩,
⟨128,584879175,584879518⟩]
theorem checked21860 : checkPrefixCuts (2^48) 2869166081 9 Manual.Count131072.C021860.packed 128 cuts21860 = true := by
 decide +kernel
def pointBounds21860 : List (Nat × Nat × Nat) := [(2869225472,101171178571520,101171559608840)]
theorem point_links_checked21860 : (cuts21860.take 1).map (fun c => (2869166081-1+2*2^9*c.k,101170907416557+c.lower,101171288453715+c.upper)) = pointBounds21860 := by
 decide +kernel
def cuts21861 : List PrefixCut := [⟨18,83187604,83187651⟩,
⟨106,497646290,497646569⟩,
⟨128,595839193,595839530⟩]
theorem checked21861 : checkPrefixCuts (2^48) 2869297153 9 Manual.Count131072.C021861.packed 128 cuts21861 = true := by
 decide +kernel
def pointBounds21861 : List (Nat × Nat × Nat) := [(2869315584,101171575483336,101171956520884),(2869405696,101171989942022,101172370979802)]
theorem point_links_checked21861 : (cuts21861.take 2).map (fun c => (2869297153-1+2*2^9*c.k,101171492295732+c.lower,101171873333233+c.upper)) = pointBounds21861 := by
 decide +kernel
def cuts21862 : List PrefixCut := [⟨66,302911991,302912161⟩,
⟨128,592084302,592084636⟩]
theorem checked21862 : checkPrefixCuts (2^48) 2869428225 9 Manual.Count131072.C021862.packed 128 cuts21862 = true := by
 decide +kernel
def pointBounds21862 : List (Nat × Nat × Nat) := [(2869495808,101172391046916,101172772084924)]
theorem point_links_checked21862 : (cuts21862.take 1).map (fun c => (2869428225-1+2*2^9*c.k,101172088134925+c.lower,101172469172763+c.upper)) = pointBounds21862 := by
 decide +kernel
def cuts21863 : List PrefixCut := [⟨26,118982546,118982615⟩,
⟨114,527222689,527222990⟩,
⟨128,592449687,592450023⟩]
theorem checked21863 : checkPrefixCuts (2^48) 2869559297 9 Manual.Count131072.C021863.packed 128 cuts21863 = true := by
 decide +kernel
def pointBounds21863 : List (Nat × Nat × Nat) := [(2869585920,101172799201773,101173180240014),(2869676032,101173207441916,101173588480389)]
theorem point_links_checked21863 : (cuts21863.take 2).map (fun c => (2869559297-1+2*2^9*c.k,101172680219227+c.lower,101173061257399+c.upper)) = pointBounds21863 := by
 decide +kernel
def cuts21864 : List PrefixCut := [⟨74,343000260,343000454⟩,
⟨128,589872414,589872751⟩]
theorem checked21864 : checkPrefixCuts (2^48) 2869690369 9 Manual.Count131072.C021864.packed 128 cuts21864 = true := by
 decide +kernel
def pointBounds21864 : List (Nat × Nat × Nat) := [(2869766144,101173615669174,101173996707876)]
theorem point_links_checked21864 : (cuts21864.take 1).map (fun c => (2869690369-1+2*2^9*c.k,101173272668914+c.lower,101173653707422+c.upper)) = pointBounds21864 := by
 decide +kernel
def cuts21865 : List PrefixCut := [⟨34,155457404,155457497⟩,
⟨122,553360787,553361111⟩,
⟨128,583470306,583470646⟩]
theorem checked21865 : checkPrefixCuts (2^48) 2869821441 9 Manual.Count131072.C021865.packed 128 cuts21865 = true := by
 decide +kernel
def pointBounds21865 : List (Nat × Nat × Nat) := [(2869856256,101174017998732,101174399037670),(2869946368,101174415902115,101174796941284)]
theorem point_links_checked21865 : (cuts21865.take 2).map (fun c => (2869821441-1+2*2^9*c.k,101173862541328+c.lower,101174243580173+c.upper)) = pointBounds21865 := by
 decide +kernel
def cuts21866 : List PrefixCut := [⟨82,379256290,379256506⟩,
⟨128,588249462,588249798⟩]
theorem checked21866 : checkPrefixCuts (2^48) 2869952513 9 Manual.Count131072.C021866.packed 128 cuts21866 = true := by
 decide +kernel
def pointBounds21866 : List (Nat × Nat × Nat) := [(2870036480,101174825267924,101175206307325)]
theorem point_links_checked21866 : (cuts21866.take 1).map (fun c => (2869952513-1+2*2^9*c.k,101174446011634+c.lower,101174827050819+c.upper)) = pointBounds21866 := by
 decide +kernel
def cuts21867 : List PrefixCut := [⟨42,194769586,194769696⟩,
⟨128,597048804,597049150⟩]
theorem checked21867 : checkPrefixCuts (2^48) 2870083585 9 Manual.Count131072.C021867.packed 128 cuts21867 = true := by
 decide +kernel
def pointBounds21867 : List (Nat × Nat × Nat) := [(2870126592,101175229030682,101175610070313)]
theorem point_links_checked21867 : (cuts21867.take 1).map (fun c => (2870083585-1+2*2^9*c.k,101175034261096+c.lower,101175415300617+c.upper)) = pointBounds21867 := by
 decide +kernel
def cuts21868 : List PrefixCut := [⟨2,9610616,9610621⟩,
⟨90,416289982,416290227⟩,
⟨128,584567330,584567676⟩]
theorem checked21868 : checkPrefixCuts (2^48) 2870214657 9 Manual.Count131072.C021868.packed 128 cuts21868 = true := by
 decide +kernel
def pointBounds21868 : List (Nat × Nat × Nat) := [(2870216704,101175640920516,101176021960388),(2870306816,101176047599882,101176428639994)]
theorem point_links_checked21868 : (cuts21868.take 2).map (fun c => (2870214657-1+2*2^9*c.k,101175631309900+c.lower,101176012349767+c.upper)) = pointBounds21868 := by
 decide +kernel
def cuts21869 : List PrefixCut := [⟨50,234074449,234074580⟩,
⟨128,599936110,599936443⟩]
theorem checked21869 : checkPrefixCuts (2^48) 2870345729 9 Manual.Count131072.C021869.packed 128 cuts21869 = true := by
 decide +kernel
def pointBounds21869 : List (Nat × Nat × Nat) := [(2870396928,101176449951679,101176830992023)]
theorem point_links_checked21869 : (cuts21869.take 1).map (fun c => (2870345729-1+2*2^9*c.k,101176215877230+c.lower,101176596917443+c.upper)) = pointBounds21869 := by
 decide +kernel
def cuts21870 : List PrefixCut := [⟨10,46479689,46479715⟩,
⟨98,452532467,452532725⟩,
⟨128,587161476,587161811⟩]
theorem checked21870 : checkPrefixCuts (2^48) 2870476801 9 Manual.Count131072.C021870.packed 128 cuts21870 = true := by
 decide +kernel
def pointBounds21870 : List (Nat × Nat × Nat) := [(2870487040,101176862293029,101177243333601),(2870577152,101177268345807,101177649386611)]
theorem point_links_checked21870 : (cuts21870.take 2).map (fun c => (2870476801-1+2*2^9*c.k,101176815813340+c.lower,101177196853886+c.upper)) = pointBounds21870 := by
 decide +kernel
def cuts21871 : List PrefixCut := [⟨58,263272546,263272694⟩,
⟨128,581153463,581153800⟩]
theorem checked21871 : checkPrefixCuts (2^48) 2870607873 9 Manual.Count131072.C021871.packed 128 cuts21871 = true := by
 decide +kernel
def pointBounds21871 : List (Nat × Nat × Nat) := [(2870667264,101177666247362,101178047288391)]
theorem point_links_checked21871 : (cuts21871.take 1).map (fun c => (2870607873-1+2*2^9*c.k,101177402974816+c.lower,101177784015697+c.upper)) = pointBounds21871 := by
 decide +kernel
def cuts21872 : List PrefixCut := [⟨18,85891198,85891249⟩,
⟨106,496219826,496220114⟩,
⟨128,594069276,594069621⟩]
theorem checked21872 : checkPrefixCuts (2^48) 2870738945 9 Manual.Count131072.C021872.packed 128 cuts21872 = true := by
 decide +kernel
def pointBounds21872 : List (Nat × Nat × Nat) := [(2870757376,101178070019477,101178451060746),(2870847488,101178480348105,101178861389611)]
theorem point_links_checked21872 : (cuts21872.take 2).map (fun c => (2870738945-1+2*2^9*c.k,101177984128279+c.lower,101178365169497+c.upper)) = pointBounds21872 := by
 decide +kernel
def cuts21873 : List PrefixCut := [⟨66,308936590,308936761⟩,
⟨128,590022330,590022659⟩]
theorem checked21873 : checkPrefixCuts (2^48) 2870870017 9 Manual.Count131072.C021873.packed 128 cuts21873 = true := by
 decide +kernel
def pointBounds21873 : List (Nat × Nat × Nat) := [(2870937600,101178887134145,101179268175879)]
theorem point_links_checked21873 : (cuts21873.take 1).map (fun c => (2870870017-1+2*2^9*c.k,101178578197555+c.lower,101178959239118+c.upper)) = pointBounds21873 := by
 decide +kernel
def cuts21874 : List PrefixCut := [⟨26,119216915,119216978⟩,
⟨114,527252018,527252312⟩,
⟨128,592838400,592838731⟩]
theorem checked21874 : checkPrefixCuts (2^48) 2871001089 9 Manual.Count131072.C021874.packed 128 cuts21874 = true := by
 decide +kernel
def pointBounds21874 : List (Nat × Nat × Nat) := [(2871027712,101179287436800,101179668478755),(2871117824,101179695471903,101180076514089)]
theorem point_links_checked21874 : (cuts21874.take 2).map (fun c => (2871001089-1+2*2^9*c.k,101179168219885+c.lower,101179549261777+c.upper)) = pointBounds21874 := by
 decide +kernel
def cuts21875 : List PrefixCut := [⟨74,341357589,341357781⟩,
⟨128,589772387,589772724⟩]
theorem checked21875 : checkPrefixCuts (2^48) 2871132161 9 Manual.Count131072.C021875.packed 128 cuts21875 = true := by
 decide +kernel
def pointBounds21875 : List (Nat × Nat × Nat) := [(2871207936,101180102415874,101180483458289)]
theorem point_links_checked21875 : (cuts21875.take 1).map (fun c => (2871132161-1+2*2^9*c.k,101179761058285+c.lower,101180142100508+c.upper)) = pointBounds21875 := by
 decide +kernel
def cuts21876 : List PrefixCut := [⟨34,153614783,153614871⟩,
⟨122,558376510,558376827⟩,
⟨128,584255731,584256064⟩]
theorem checked21876 : checkPrefixCuts (2^48) 2871263233 9 Manual.Count131072.C021876.packed 128 cuts21876 = true := by
 decide +kernel
def pointBounds21876 : List (Nat × Nat × Nat) := [(2871298048,101180504445455,101180885488103),(2871388160,101180909207182,101181290250059)]
theorem point_links_checked21876 : (cuts21876.take 2).map (fun c => (2871263233-1+2*2^9*c.k,101180350830672+c.lower,101180731873232+c.upper)) = pointBounds21876 := by
 decide +kernel
def cuts21877 : List PrefixCut := [⟨82,381124324,381124546⟩,
⟨128,588738265,588738606⟩]
theorem checked21877 : checkPrefixCuts (2^48) 2871394305 9 Manual.Count131072.C021877.packed 128 cuts21877 = true := by
 decide +kernel
def pointBounds21877 : List (Nat × Nat × Nat) := [(2871478272,101181316210727,101181697253842)]
theorem point_links_checked21877 : (cuts21877.take 1).map (fun c => (2871394305-1+2*2^9*c.k,101180935086403+c.lower,101181316129296+c.upper)) = pointBounds21877 := by
 decide +kernel
def cuts21878 : List PrefixCut := [⟨42,195651997,195652107⟩,
⟨128,593514376,593514710⟩]
theorem checked21878 : checkPrefixCuts (2^48) 2871525377 9 Manual.Count131072.C021878.packed 128 cuts21878 = true := by
 decide +kernel
def pointBounds21878 : List (Nat × Nat × Nat) := [(2871568384,101181719476665,101182100520009)]
theorem point_links_checked21878 : (cuts21878.take 1).map (fun c => (2871525377-1+2*2^9*c.k,101181523824668+c.lower,101181904867902+c.upper)) = pointBounds21878 := by
 decide +kernel
def cuts21879 : List PrefixCut := [⟨2,9507772,9507777⟩,
⟨90,415591003,415591234⟩,
⟨128,593879389,593879723⟩]
theorem checked21879 : checkPrefixCuts (2^48) 2871656449 9 Manual.Count131072.C021879.packed 128 cuts21879 = true := by
 decide +kernel
def pointBounds21879 : List (Nat × Nat × Nat) := [(2871658496,101182126846816,101182507890389),(2871748608,101182532930047,101182913973846)]
theorem point_links_checked21879 : (cuts21879.take 2).map (fun c => (2871656449-1+2*2^9*c.k,101182117339044+c.lower,101182498382612+c.upper)) = pointBounds21879 := by
 decide +kernel
def cuts21880 : List PrefixCut := [⟨50,237485399,237485534⟩,
⟨128,594440428,594440771⟩]
theorem checked21880 : checkPrefixCuts (2^48) 2871787521 9 Manual.Count131072.C021880.packed 128 cuts21880 = true := by
 decide +kernel
def pointBounds21880 : List (Nat × Nat × Nat) := [(2871838720,101182948703832,101183329747869)]
theorem point_links_checked21880 : (cuts21880.take 1).map (fun c => (2871787521-1+2*2^9*c.k,101182711218433+c.lower,101183092262335+c.upper)) = pointBounds21880 := by
 decide +kernel
def cuts21881 : List PrefixCut := [⟨10,47142417,47142442⟩,
⟨98,454461497,454461759⟩,
⟨128,592747128,592747472⟩]
theorem checked21881 : checkPrefixCuts (2^48) 2871918593 9 Manual.Count131072.C021881.packed 128 cuts21881 = true := by
 decide +kernel
def pointBounds21881 : List (Nat × Nat × Nat) := [(2871928832,101183352801278,101183733845548),(2872018944,101183760120358,101184141164865)]
theorem point_links_checked21881 : (cuts21881.take 2).map (fun c => (2871918593-1+2*2^9*c.k,101183305658861+c.lower,101183686703106+c.upper)) = pointBounds21881 := by
 decide +kernel
def cuts21882 : List PrefixCut := [⟨58,270588695,270588846⟩,
⟨128,589878025,589878355⟩]
theorem checked21882 : checkPrefixCuts (2^48) 2872049665 9 Manual.Count131072.C021882.packed 128 cuts21882 = true := by
 decide +kernel
def pointBounds21882 : List (Nat × Nat × Nat) := [(2872109056,101184168994684,101184550039424)]
theorem point_links_checked21882 : (cuts21882.take 1).map (fun c => (2872049665-1+2*2^9*c.k,101183898405989+c.lower,101184279450578+c.upper)) = pointBounds21882 := by
 decide +kernel
def cuts21883 : List PrefixCut := [⟨18,82222088,82222134⟩,
⟨106,491070785,491071062⟩,
⟨128,588577137,588577468⟩]
theorem checked21883 : checkPrefixCuts (2^48) 2872180737 9 Manual.Count131072.C021883.packed 128 cuts21883 = true := by
 decide +kernel
def pointBounds21883 : List (Nat × Nat × Nat) := [(2872199168,101184570506102,101184951551067),(2872289280,101184979354799,101185360399995)]
theorem point_links_checked21883 : (cuts21883.take 2).map (fun c => (2872180737-1+2*2^9*c.k,101184488284014+c.lower,101184869328933+c.upper)) = pointBounds21883 := by
 decide +kernel
def cuts21884 : List PrefixCut := [⟨66,306919715,306919893⟩,
⟨128,594331829,594332172⟩]
theorem checked21884 : checkPrefixCuts (2^48) 2872311809 9 Manual.Count131072.C021884.packed 128 cuts21884 = true := by
 decide +kernel
def pointBounds21884 : List (Nat × Nat × Nat) := [(2872379392,101185383780866,101185764826294)]
theorem point_links_checked21884 : (cuts21884.take 1).map (fun c => (2872311809-1+2*2^9*c.k,101185076861151+c.lower,101185457906401+c.upper)) = pointBounds21884 := by
 decide +kernel
def cuts21885 : List PrefixCut := [⟨26,116609307,116609373⟩,
⟨114,515522619,515522912⟩,
⟨128,581272058,581272389⟩]
theorem checked21885 : checkPrefixCuts (2^48) 2872442881 9 Manual.Count131072.C021885.packed 128 cuts21885 = true := by
 decide +kernel
def pointBounds21885 : List (Nat × Nat × Nat) := [(2872469504,101185787802287,101186168847946),(2872559616,101186186715599,101186567761485)]
theorem point_links_checked21885 : (cuts21885.take 2).map (fun c => (2872442881-1+2*2^9*c.k,101185671192980+c.lower,101186052238573+c.upper)) = pointBounds21885 := by
 decide +kernel
def cuts21886 : List PrefixCut := [⟨74,339814391,339814583⟩,
⟨128,591239986,591240319⟩]
theorem checked21886 : checkPrefixCuts (2^48) 2872573953 9 Manual.Count131072.C021886.packed 128 cuts21886 = true := by
 decide +kernel
def pointBounds21886 : List (Nat × Nat × Nat) := [(2872649728,101186592279429,101186973325545)]
theorem point_links_checked21886 : (cuts21886.take 1).map (fun c => (2872573953-1+2*2^9*c.k,101186252465038+c.lower,101186633510962+c.upper)) = pointBounds21886 := by
 decide +kernel
def cuts21887 : List PrefixCut := [⟨34,156281194,156281278⟩,
⟨122,565248896,565249214⟩,
⟨128,592290868,592291203⟩]
theorem checked21887 : checkPrefixCuts (2^48) 2872705025 9 Manual.Count131072.C021887.packed 128 cuts21887 = true := by
 decide +kernel
def pointBounds21887 : List (Nat × Nat × Nat) := [(2872739840,101186999986218,101187381032559),(2872829952,101187408953920,101187790000495)]
theorem point_links_checked21887 : (cuts21887.take 2).map (fun c => (2872705025-1+2*2^9*c.k,101186843705024+c.lower,101187224751281+c.upper)) = pointBounds21887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000058
