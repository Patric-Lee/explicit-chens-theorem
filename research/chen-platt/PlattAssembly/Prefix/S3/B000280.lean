import PlattAssemblyKernel
import PlattCertificates.Count131072.C028960
import PlattCertificates.Count131072.C028961
import PlattCertificates.Count131072.C028962
import PlattCertificates.Count131072.C028963
import PlattCertificates.Count131072.C028964
import PlattCertificates.Count131072.C028965
import PlattCertificates.Count131072.C028966
import PlattCertificates.Count131072.C028967
import PlattCertificates.Count131072.C028968
import PlattCertificates.Count131072.C028969
import PlattCertificates.Count131072.C028970
import PlattCertificates.Count131072.C028971
import PlattCertificates.Count131072.C028972
import PlattCertificates.Count131072.C028973
import PlattCertificates.Count131072.C028974
import PlattCertificates.Count131072.C028975
import PlattCertificates.Count131072.C028976
import PlattCertificates.Count131072.C028977
import PlattCertificates.Count131072.C028978
import PlattCertificates.Count131072.C028979
import PlattCertificates.Count131072.C028980
import PlattCertificates.Count131072.C028981
import PlattCertificates.Count131072.C028982
import PlattCertificates.Count131072.C028983
import PlattCertificates.Count131072.C028984
import PlattCertificates.Count131072.C028985
import PlattCertificates.Count131072.C028986
import PlattCertificates.Count131072.C028987
import PlattCertificates.Count131072.C028988
import PlattCertificates.Count131072.C028989
import PlattCertificates.Count131072.C028990
import PlattCertificates.Count131072.C028991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000280
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28960 : List PrefixCut := [⟨11,34223377,34223397⟩,
⟨127,438007919,438008159⟩,
⟨128,442452367,442452610⟩]
theorem checked28960 : checkPrefixCuts (2^48) 3799777281 9 Manual.Count131072.C028960.packed 128 cuts28960 = true := by
 decide +kernel
def pointBounds28960 : List (Nat × Nat × Nat) := [(3799788544,104778656134437,104779039203689),(3799907328,104779059918979,104779442988451)]
theorem point_links_checked28960 : (cuts28960.take 2).map (fun c => (3799777281-1+2*2^9*c.k,104778621911060+c.lower,104779004980292+c.upper)) = pointBounds28960 := by
 decide +kernel
def cuts28961 : List PrefixCut := [⟨115,398957111,398957332⟩,
⟨128,445103785,445104031⟩]
theorem checked28961 : checkPrefixCuts (2^48) 3799908353 9 Manual.Count131072.C028961.packed 128 cuts28961 = true := by
 decide +kernel
def pointBounds28961 : List (Nat × Nat × Nat) := [(3800026112,104779463320538,104779846390234)]
theorem point_links_checked28961 : (cuts28961.take 1).map (fun c => (3799908353-1+2*2^9*c.k,104779064363427+c.lower,104779447432902+c.upper)) = pointBounds28961 := by
 decide +kernel
def cuts28962 : List PrefixCut := [⟨103,353612750,353612949⟩,
⟨128,438866475,438866720⟩]
theorem checked28962 : checkPrefixCuts (2^48) 3800039425 9 Manual.Count131072.C028962.packed 128 cuts28962 = true := by
 decide +kernel
def pointBounds28962 : List (Nat × Nat × Nat) := [(3800144896,104779863079962,104780246149882)]
theorem point_links_checked28962 : (cuts28962.take 1).map (fun c => (3800039425-1+2*2^9*c.k,104779509467212+c.lower,104779892536933+c.upper)) = pointBounds28962 := by
 decide +kernel
def cuts28963 : List PrefixCut := [⟨91,313974713,313974891⟩,
⟨128,445369279,445369530⟩]
theorem checked28963 : checkPrefixCuts (2^48) 3800170497 9 Manual.Count131072.C028963.packed 128 cuts28963 = true := by
 decide +kernel
def pointBounds28963 : List (Nat × Nat × Nat) := [(3800263680,104780262308400,104780645378544)]
theorem point_links_checked28963 : (cuts28963.take 1).map (fun c => (3800170497-1+2*2^9*c.k,104779948333687+c.lower,104780331403653+c.upper)) = pointBounds28963 := by
 decide +kernel
def cuts28964 : List PrefixCut := [⟨79,270487841,270487989⟩,
⟨128,438539959,438540204⟩]
theorem checked28964 : checkPrefixCuts (2^48) 3800301569 9 Manual.Count131072.C028964.packed 128 cuts28964 = true := by
 decide +kernel
def pointBounds28964 : List (Nat × Nat × Nat) := [(3800382464,104780664190807,104781047261172)]
theorem point_links_checked28964 : (cuts28964.take 1).map (fun c => (3800301569-1+2*2^9*c.k,104780393702966+c.lower,104780776773183+c.upper)) = pointBounds28964 := by
 decide +kernel
def cuts28965 : List PrefixCut := [⟨67,229447904,229448030⟩,
⟨128,440746711,440746954⟩]
theorem checked28965 : checkPrefixCuts (2^48) 3800432641 9 Manual.Count131072.C028965.packed 128 cuts28965 = true := by
 decide +kernel
def pointBounds28965 : List (Nat × Nat × Nat) := [(3800501248,104781061690829,104781444761417)]
theorem point_links_checked28965 : (cuts28965.take 1).map (fun c => (3800432641-1+2*2^9*c.k,104780832242925+c.lower,104781215313387+c.upper)) = pointBounds28965 := by
 decide +kernel
def cuts28966 : List PrefixCut := [⟨55,188188510,188188618⟩,
⟨128,434584589,434584835⟩]
theorem checked28966 : checkPrefixCuts (2^48) 3800563713 9 Manual.Count131072.C028966.packed 128 cuts28966 = true := by
 decide +kernel
def pointBounds28966 : List (Nat × Nat × Nat) := [(3800620032,104781461178146,104781844248959)]
theorem point_links_checked28966 : (cuts28966.take 1).map (fun c => (3800563713-1+2*2^9*c.k,104781272989636+c.lower,104781656060341+c.upper)) = pointBounds28966 := by
 decide +kernel
def cuts28967 : List PrefixCut := [⟨43,149523871,149523951⟩,
⟨128,442419667,442419907⟩]
theorem checked28967 : checkPrefixCuts (2^48) 3800694785 9 Manual.Count131072.C028967.packed 128 cuts28967 = true := by
 decide +kernel
def pointBounds28967 : List (Nat × Nat × Nat) := [(3800738816,104781857098096,104782240169127)]
theorem point_links_checked28967 : (cuts28967.take 1).map (fun c => (3800694785-1+2*2^9*c.k,104781707574225+c.lower,104782090645176+c.upper)) = pointBounds28967 := by
 decide +kernel
def cuts28968 : List PrefixCut := [⟨31,104937268,104937327⟩,
⟨128,439960558,439960808⟩]
theorem checked28968 : checkPrefixCuts (2^48) 3800825857 9 Manual.Count131072.C028968.packed 128 cuts28968 = true := by
 decide +kernel
def pointBounds28968 : List (Nat × Nat × Nat) := [(3800857600,104782254931160,104782638002410)]
theorem point_links_checked28968 : (cuts28968.take 1).map (fun c => (3800825857-1+2*2^9*c.k,104782149993892+c.lower,104782533065083+c.upper)) = pointBounds28968 := by
 decide +kernel
def cuts28969 : List PrefixCut := [⟨19,64204389,64204425⟩,
⟨128,437057330,437057578⟩]
theorem checked28969 : checkPrefixCuts (2^48) 3800956929 9 Manual.Count131072.C028969.packed 128 cuts28969 = true := by
 decide +kernel
def pointBounds28969 : List (Nat × Nat × Nat) := [(3800976384,104782654158839,104783037230316)]
theorem point_links_checked28969 : (cuts28969.take 1).map (fun c => (3800956929-1+2*2^9*c.k,104782589954450+c.lower,104782973025891+c.upper)) = pointBounds28969 := by
 decide +kernel
def cuts28970 : List PrefixCut := [⟨7,23548238,23548252⟩,
⟨123,425268654,425268896⟩,
⟨128,442521985,442522237⟩]
theorem checked28970 : checkPrefixCuts (2^48) 3801088001 9 Manual.Count131072.C028970.packed 128 cuts28970 = true := by
 decide +kernel
def pointBounds28970 : List (Nat × Nat × Nat) := [(3801095168,104783050560018,104783433631721),(3801213952,104783452280434,104783835352365)]
theorem point_links_checked28970 : (cuts28970.take 2).map (fun c => (3801088001-1+2*2^9*c.k,104783027011780+c.lower,104783410083469+c.upper)) = pointBounds28970 := by
 decide +kernel
def cuts28971 : List PrefixCut := [⟨112,385417033,385417251⟩,
⟨128,440581448,440581696⟩]
theorem checked28971 : checkPrefixCuts (2^48) 3801219073 9 Manual.Count131072.C028971.packed 128 cuts28971 = true := by
 decide +kernel
def pointBounds28971 : List (Nat × Nat × Nat) := [(3801333760,104783854950798,104784238022957)]
theorem point_links_checked28971 : (cuts28971.take 1).map (fun c => (3801219073-1+2*2^9*c.k,104783469533765+c.lower,104783852605706+c.upper)) = pointBounds28971 := by
 decide +kernel
def cuts28972 : List PrefixCut := [⟨101,345494094,345494291⟩,
⟨128,439899872,439900119⟩]
theorem checked28972 : checkPrefixCuts (2^48) 3801350145 9 Manual.Count131072.C028972.packed 128 cuts28972 = true := by
 decide +kernel
def pointBounds28972 : List (Nat × Nat × Nat) := [(3801453568,104784255609307,104784638681693)]
theorem point_links_checked28972 : (cuts28972.take 1).map (fun c => (3801350145-1+2*2^9*c.k,104783910115213+c.lower,104784293187402+c.upper)) = pointBounds28972 := by
 decide +kernel
def cuts28973 : List PrefixCut := [⟨90,309497987,309498161⟩,
⟨128,439810669,439810916⟩]
theorem checked28973 : checkPrefixCuts (2^48) 3801481217 9 Manual.Count131072.C028973.packed 128 cuts28973 = true := by
 decide +kernel
def pointBounds28973 : List (Nat × Nat × Nat) := [(3801573376,104784659513072,104785042585682)]
theorem point_links_checked28973 : (cuts28973.take 1).map (fun c => (3801481217-1+2*2^9*c.k,104784350015085+c.lower,104784733087521+c.upper)) = pointBounds28973 := by
 decide +kernel
def cuts28974 : List PrefixCut := [⟨79,269728217,269728369⟩,
⟨128,438018554,438018798⟩]
theorem checked28974 : checkPrefixCuts (2^48) 3801612289 9 Manual.Count131072.C028974.packed 128 cuts28974 = true := by
 decide +kernel
def pointBounds28974 : List (Nat × Nat × Nat) := [(3801693184,104785059553971,104785442626806)]
theorem point_links_checked28974 : (cuts28974.take 1).map (fun c => (3801612289-1+2*2^9*c.k,104784789825754+c.lower,104785172898437+c.upper)) = pointBounds28974 := by
 decide +kernel
def cuts28975 : List PrefixCut := [⟨68,238919672,238919806⟩,
⟨128,443186158,443186408⟩]
theorem checked28975 : checkPrefixCuts (2^48) 3801743361 9 Manual.Count131072.C028975.packed 128 cuts28975 = true := by
 decide +kernel
def pointBounds28975 : List (Nat × Nat × Nat) := [(3801812992,104785466763980,104785849837041)]
theorem point_links_checked28975 : (cuts28975.take 1).map (fun c => (3801743361-1+2*2^9*c.k,104785227844308+c.lower,104785610917235+c.upper)) = pointBounds28975 := by
 decide +kernel
def cuts28976 : List PrefixCut := [⟨57,198488504,198488617⟩,
⟨128,443392891,443393137⟩]
theorem checked28976 : checkPrefixCuts (2^48) 3801874433 9 Manual.Count131072.C028976.packed 128 cuts28976 = true := by
 decide +kernel
def pointBounds28976 : List (Nat × Nat × Nat) := [(3801932800,104785869518970,104786252592260)]
theorem point_links_checked28976 : (cuts28976.take 1).map (fun c => (3801874433-1+2*2^9*c.k,104785671030466+c.lower,104786054103643+c.upper)) = pointBounds28976 := by
 decide +kernel
def cuts28977 : List PrefixCut := [⟨46,155913092,155913180⟩,
⟨128,440046131,440046375⟩]
theorem checked28977 : checkPrefixCuts (2^48) 3802005505 9 Manual.Count131072.C028977.packed 128 cuts28977 = true := by
 decide +kernel
def pointBounds28977 : List (Nat × Nat × Nat) := [(3802052608,104786270336449,104786653409960)]
theorem point_links_checked28977 : (cuts28977.take 1).map (fun c => (3802005505-1+2*2^9*c.k,104786114423357+c.lower,104786497496780+c.upper)) = pointBounds28977 := by
 decide +kernel
def cuts28978 : List PrefixCut := [⟨35,119410978,119411046⟩,
⟨128,440623182,440623429⟩]
theorem checked28978 : checkPrefixCuts (2^48) 3802136577 9 Manual.Count131072.C028978.packed 128 cuts28978 = true := by
 decide +kernel
def pointBounds28978 : List (Nat × Nat × Nat) := [(3802172416,104786673880466,104787056954201)]
theorem point_links_checked28978 : (cuts28978.take 1).map (fun c => (3802136577-1+2*2^9*c.k,104786554469488+c.lower,104786937543155+c.upper)) = pointBounds28978 := by
 decide +kernel
def cuts28979 : List PrefixCut := [⟨24,81800863,81800909⟩,
⟨128,443643098,443643350⟩]
theorem checked28979 : checkPrefixCuts (2^48) 3802267649 9 Manual.Count131072.C028979.packed 128 cuts28979 = true := by
 decide +kernel
def pointBounds28979 : List (Nat × Nat × Nat) := [(3802292224,104787076893533,104787459967493)]
theorem point_links_checked28979 : (cuts28979.take 1).map (fun c => (3802267649-1+2*2^9*c.k,104786995092670+c.lower,104787378166584+c.upper)) = pointBounds28979 := by
 decide +kernel
def cuts28980 : List PrefixCut := [⟨13,46339953,46339977⟩,
⟨128,437261835,437262079⟩]
theorem checked28980 : checkPrefixCuts (2^48) 3802398721 9 Manual.Count131072.C028980.packed 128 cuts28980 = true := by
 decide +kernel
def pointBounds28980 : List (Nat × Nat × Nat) := [(3802412032,104787485075721,104787868149911)]
theorem point_links_checked28980 : (cuts28980.take 1).map (fun c => (3802398721-1+2*2^9*c.k,104787438735768+c.lower,104787821809934+c.upper)) = pointBounds28980 := by
 decide +kernel
def cuts28981 : List PrefixCut := [⟨2,6884143,6884147⟩,
⟨119,411857726,411857956⟩,
⟨128,442280193,442280440⟩]
theorem checked28981 : checkPrefixCuts (2^48) 3802529793 9 Manual.Count131072.C028981.packed 128 cuts28981 = true := by
 decide +kernel
def pointBounds28981 : List (Nat × Nat × Nat) := [(3802531840,104787882881746,104788265956160),(3802651648,104788287855329,104788670929969)]
theorem point_links_checked28981 : (cuts28981.take 2).map (fun c => (3802529793-1+2*2^9*c.k,104787875997603+c.lower,104788259072013+c.upper)) = pointBounds28981 := by
 decide +kernel
def cuts28982 : List PrefixCut := [⟨108,366840296,366840501⟩,
⟨128,434640929,434641171⟩]
theorem checked28982 : checkPrefixCuts (2^48) 3802660865 9 Manual.Count131072.C028982.packed 128 cuts28982 = true := by
 decide +kernel
def pointBounds28982 : List (Nat × Nat × Nat) := [(3802771456,104788685118092,104789068192954)]
theorem point_links_checked28982 : (cuts28982.take 1).map (fun c => (3802660865-1+2*2^9*c.k,104788318277796+c.lower,104788701352453+c.upper)) = pointBounds28982 := by
 decide +kernel
def cuts28983 : List PrefixCut := [⟨97,335074909,335075096⟩,
⟨128,442619746,442619993⟩]
theorem checked28983 : checkPrefixCuts (2^48) 3802791937 9 Manual.Count131072.C028983.packed 128 cuts28983 = true := by
 decide +kernel
def pointBounds28983 : List (Nat × Nat × Nat) := [(3802891264,104789087993634,104789471068720)]
theorem point_links_checked28983 : (cuts28983.take 1).map (fun c => (3802791937-1+2*2^9*c.k,104788752918725+c.lower,104789135993624+c.upper)) = pointBounds28983 := by
 decide +kernel
def cuts28984 : List PrefixCut := [⟨86,302127369,302127538⟩,
⟨128,445491085,445491335⟩]
theorem checked28984 : checkPrefixCuts (2^48) 3802923009 9 Manual.Count131072.C028984.packed 128 cuts28984 = true := by
 decide +kernel
def pointBounds28984 : List (Nat × Nat × Nat) := [(3803011072,104789497665840,104789880741155)]
theorem point_links_checked28984 : (cuts28984.take 1).map (fun c => (3802923009-1+2*2^9*c.k,104789195538471+c.lower,104789578613617+c.upper)) = pointBounds28984 := by
 decide +kernel
def cuts28985 : List PrefixCut := [⟨75,262891021,262891166⟩,
⟨128,441775222,441775462⟩]
theorem checked28985 : checkPrefixCuts (2^48) 3803054081 9 Manual.Count131072.C028985.packed 128 cuts28985 = true := by
 decide +kernel
def pointBounds28985 : List (Nat × Nat × Nat) := [(3803130880,104789903920577,104790286996118)]
theorem point_links_checked28985 : (cuts28985.take 1).map (fun c => (3803054081-1+2*2^9*c.k,104789641029556+c.lower,104790024104952+c.upper)) = pointBounds28985 := by
 decide +kernel
def cuts28986 : List PrefixCut := [⟨64,222917108,222917231⟩,
⟨128,447088511,447088757⟩]
theorem checked28986 : checkPrefixCuts (2^48) 3803185153 9 Manual.Count131072.C028986.packed 128 cuts28986 = true := by
 decide +kernel
def pointBounds28986 : List (Nat × Nat × Nat) := [(3803250688,104790305721886,104790688797645)]
theorem point_links_checked28986 : (cuts28986.take 1).map (fun c => (3803185153-1+2*2^9*c.k,104790082804778+c.lower,104790465880414+c.upper)) = pointBounds28986 := by
 decide +kernel
def cuts28987 : List PrefixCut := [⟨53,181391710,181391810⟩,
⟨128,436638268,436638511⟩]
theorem checked28987 : checkPrefixCuts (2^48) 3803316225 9 Manual.Count131072.C028987.packed 128 cuts28987 = true := by
 decide +kernel
def pointBounds28987 : List (Nat × Nat × Nat) := [(3803370496,104790711284999,104791094360981)]
theorem point_links_checked28987 : (cuts28987.take 1).map (fun c => (3803316225-1+2*2^9*c.k,104790529893289+c.lower,104790912969171+c.upper)) = pointBounds28987 := by
 decide +kernel
def cuts28988 : List PrefixCut := [⟨42,141793169,141793249⟩,
⟨128,438103269,438103516⟩]
theorem checked28988 : checkPrefixCuts (2^48) 3803447297 9 Manual.Count131072.C028988.packed 128 cuts28988 = true := by
 decide +kernel
def pointBounds28988 : List (Nat × Nat × Nat) := [(3803490304,104791108324726,104791491400931)]
theorem point_links_checked28988 : (cuts28988.take 1).map (fun c => (3803447297-1+2*2^9*c.k,104790966531557+c.lower,104791349607682+c.upper)) = pointBounds28988 := by
 decide +kernel
def cuts28989 : List PrefixCut := [⟨31,107599409,107599468⟩,
⟨128,439938225,439938469⟩]
theorem checked28989 : checkPrefixCuts (2^48) 3803578369 9 Manual.Count131072.C028989.packed 128 cuts28989 = true := by
 decide +kernel
def pointBounds28989 : List (Nat × Nat × Nat) := [(3803610112,104791512234235,104791895310666)]
theorem point_links_checked28989 : (cuts28989.take 1).map (fun c => (3803578369-1+2*2^9*c.k,104791404634826+c.lower,104791787711198+c.upper)) = pointBounds28989 := by
 decide +kernel
def cuts28990 : List PrefixCut := [⟨20,69189916,69189952⟩,
⟨128,443178988,443179239⟩]
theorem checked28990 : checkPrefixCuts (2^48) 3803709441 9 Manual.Count131072.C028990.packed 128 cuts28990 = true := by
 decide +kernel
def pointBounds28990 : List (Nat × Nat × Nat) := [(3803729920,104791913762967,104792296839619)]
theorem point_links_checked28990 : (cuts28990.take 1).map (fun c => (3803709441-1+2*2^9*c.k,104791844573051+c.lower,104792227649667+c.upper)) = pointBounds28990 := by
 decide +kernel
def cuts28991 : List PrefixCut := [⟨9,31374924,31374942⟩,
⟨126,430214452,430214695⟩,
⟨128,437761945,437762192⟩]
theorem checked28991 : checkPrefixCuts (2^48) 3803840513 9 Manual.Count131072.C028991.packed 128 cuts28991 = true := by
 decide +kernel
def pointBounds28991 : List (Nat × Nat × Nat) := [(3803849728,104792319126963,104792702203848),(3803969536,104792717966491,104793101043601)]
theorem point_links_checked28991 : (cuts28991.take 2).map (fun c => (3803840513-1+2*2^9*c.k,104792287752039+c.lower,104792670828906+c.upper)) = pointBounds28991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000280
