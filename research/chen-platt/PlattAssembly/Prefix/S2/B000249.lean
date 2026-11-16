import PlattAssemblyKernel
import PlattCertificates.Count131072.C017968
import PlattCertificates.Count131072.C017969
import PlattCertificates.Count131072.C017970
import PlattCertificates.Count131072.C017971
import PlattCertificates.Count131072.C017972
import PlattCertificates.Count131072.C017973
import PlattCertificates.Count131072.C017974
import PlattCertificates.Count131072.C017975
import PlattCertificates.Count131072.C017976
import PlattCertificates.Count131072.C017977
import PlattCertificates.Count131072.C017978
import PlattCertificates.Count131072.C017979
import PlattCertificates.Count131072.C017980
import PlattCertificates.Count131072.C017981
import PlattCertificates.Count131072.C017982
import PlattCertificates.Count131072.C017983
import PlattCertificates.Count131072.C017984
import PlattCertificates.Count131072.C017985
import PlattCertificates.Count131072.C017986
import PlattCertificates.Count131072.C017987
import PlattCertificates.Count131072.C017988
import PlattCertificates.Count131072.C017989
import PlattCertificates.Count131072.C017990
import PlattCertificates.Count131072.C017991
import PlattCertificates.Count131072.C017992
import PlattCertificates.Count131072.C017993
import PlattCertificates.Count131072.C017994
import PlattCertificates.Count131072.C017995
import PlattCertificates.Count131072.C017996
import PlattCertificates.Count131072.C017997
import PlattCertificates.Count131072.C017998
import PlattCertificates.Count131072.C017999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000249
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17968 : List PrefixCut := [⟨44,246985636,246985787⟩,
⟨116,651459209,651459609⟩,
⟨128,722091648,722092088⟩]
theorem checked17968 : checkPrefixCuts (2^48) 2359033857 9 Manual.Count131072.C017968.packed 128 cuts17968 = true := by
 decide +kernel
def pointBounds17968 : List (Nat × Nat × Nat) := [(2359078912,98629339827908,98629719364476),(2359152640,98629744301481,98630123838298)]
theorem point_links_checked17968 : (cuts17968.take 2).map (fun c => (2359033857-1+2*2^9*c.k,98629092842272+c.lower,98629472378689+c.upper)) = pointBounds17968 := by
 decide +kernel
def cuts17969 : List PrefixCut := [⟨60,335498900,335499103⟩,
⟨128,712507060,712507499⟩]
theorem checked17969 : checkPrefixCuts (2^48) 2359164929 9 Manual.Count131072.C017969.packed 128 cuts17969 = true := by
 decide +kernel
def pointBounds17969 : List (Nat × Nat × Nat) := [(2359226368,98630150432820,98630529969880)]
theorem point_links_checked17969 : (cuts17969.take 1).map (fun c => (2359164929-1+2*2^9*c.k,98629814933920+c.lower,98630194470777+c.upper)) = pointBounds17969 := by
 decide +kernel
def cuts17970 : List PrefixCut := [⟨4,24696034,24696049⟩,
⟨76,429131554,429131824⟩,
⟨128,726306196,726306647⟩]
theorem checked17970 : checkPrefixCuts (2^48) 2359296001 9 Manual.Count131072.C017970.packed 128 cuts17970 = true := by
 decide +kernel
def pointBounds17970 : List (Nat × Nat × Nat) := [(2359300096,98630552137014,98630931674325),(2359373824,98630956572534,98631336110100)]
theorem point_links_checked17970 : (cuts17970.take 2).map (fun c => (2359296001-1+2*2^9*c.k,98630527440980+c.lower,98630906978276+c.upper)) = pointBounds17970 := by
 decide +kernel
def cuts17971 : List PrefixCut := [⟨21,120728998,120729070⟩,
⟨94,539215888,539216218⟩,
⟨128,731992117,731992565⟩]
theorem checked17971 : checkPrefixCuts (2^48) 2359427073 9 Manual.Count131072.C017971.packed 128 cuts17971 = true := by
 decide +kernel
def pointBounds17971 : List (Nat × Nat × Nat) := [(2359448576,98631374476174,98631754013993),(2359523328,98631792963064,98632172501141)]
theorem point_links_checked17971 : (cuts17971.take 2).map (fun c => (2359427073-1+2*2^9*c.k,98631253747176+c.lower,98631633284923+c.upper)) = pointBounds17971 := by
 decide +kernel
def cuts17972 : List PrefixCut := [⟨39,221760738,221760871⟩,
⟨112,632228864,632229248⟩,
⟨128,721692727,721693166⟩]
theorem checked17972 : checkPrefixCuts (2^48) 2359558145 9 Manual.Count131072.C017972.packed 128 cuts17972 = true := by
 decide +kernel
def pointBounds17972 : List (Nat × Nat × Nat) := [(2359598080,98632207500031,98632587038359),(2359672832,98632617968157,98632997506736)]
theorem point_links_checked17972 : (cuts17972.take 2).map (fun c => (2359558145-1+2*2^9*c.k,98631985739293+c.lower,98632365277488+c.upper)) = pointBounds17972 := by
 decide +kernel
def cuts17973 : List PrefixCut := [⟨57,326836065,326836263⟩,
⟨128,734057827,734058269⟩]
theorem checked17973 : checkPrefixCuts (2^48) 2359689217 9 Manual.Count131072.C017973.packed 128 cuts17973 = true := by
 decide +kernel
def pointBounds17973 : List (Nat × Nat × Nat) := [(2359747584,98633034268085,98633413806917)]
theorem point_links_checked17973 : (cuts17973.take 1).map (fun c => (2359689217-1+2*2^9*c.k,98632707432020+c.lower,98633086970654+c.upper)) = pointBounds17973 := by
 decide +kernel
def cuts17974 : List PrefixCut := [⟨2,10496468,10496476⟩,
⟨75,423907543,423907808⟩,
⟨128,723401669,723402115⟩]
theorem checked17974 : checkPrefixCuts (2^48) 2359820289 9 Manual.Count131072.C017974.packed 128 cuts17974 = true := by
 decide +kernel
def pointBounds17974 : List (Nat × Nat × Nat) := [(2359822336,98633451986315,98633831525399),(2359897088,98633865397390,98634244936731)]
theorem point_links_checked17974 : (cuts17974.take 2).map (fun c => (2359820289-1+2*2^9*c.k,98633441489847+c.lower,98633821028923+c.upper)) = pointBounds17974 := by
 decide +kernel
def cuts17975 : List PrefixCut := [⟨20,106389672,106389740⟩,
⟨93,519178124,519178447⟩,
⟨128,717755624,717756067⟩]
theorem checked17975 : checkPrefixCuts (2^48) 2359951361 9 Manual.Count131072.C017975.packed 128 cuts17975 = true := by
 decide +kernel
def pointBounds17975 : List (Nat × Nat × Nat) := [(2359971840,98634271281188,98634650820778),(2360046592,98634684069640,98635063609485)]
theorem point_links_checked17975 : (cuts17975.take 2).map (fun c => (2359951361-1+2*2^9*c.k,98634164891516+c.lower,98634544431038+c.upper)) = pointBounds17975 := by
 decide +kernel
def cuts17976 : List PrefixCut := [⟨38,217775814,217775945⟩,
⟨111,626364016,626364396⟩,
⟨128,721413173,721413610⟩]
theorem checked17976 : checkPrefixCuts (2^48) 2360082433 9 Manual.Count131072.C017976.packed 128 cuts17976 = true := by
 decide +kernel
def pointBounds17976 : List (Nat × Nat × Nat) := [(2360121344,98635100422954,98635479963050),(2360196096,98635509011156,98635888551501)]
theorem point_links_checked17976 : (cuts17976.take 2).map (fun c => (2360082433-1+2*2^9*c.k,98634882647140+c.lower,98635262187105+c.upper)) = pointBounds17976 := by
 decide +kernel
def cuts17977 : List PrefixCut := [⟨56,318892668,318892863⟩,
⟨128,723758139,723758586⟩]
theorem checked17977 : checkPrefixCuts (2^48) 2360213505 9 Manual.Count131072.C017977.packed 128 cuts17977 = true := by
 decide +kernel
def pointBounds17977 : List (Nat × Nat × Nat) := [(2360270848,98635922952981,98636302493578)]
theorem point_links_checked17977 : (cuts17977.take 1).map (fun c => (2360213505-1+2*2^9*c.k,98635604060313+c.lower,98635983600715+c.upper)) = pointBounds17977 := by
 decide +kernel
def cuts17978 : List PrefixCut := [⟨1,5127818,5127821⟩,
⟨74,414750429,414750677⟩,
⟨128,721213641,721214076⟩]
theorem checked17978 : checkPrefixCuts (2^48) 2360344577 9 Manual.Count131072.C017978.packed 128 cuts17978 = true := by
 decide +kernel
def pointBounds17978 : List (Nat × Nat × Nat) := [(2360345600,98636332946270,98636712487122),(2360420352,98636742568881,98637122109978)]
theorem point_links_checked17978 : (cuts17978.take 2).map (fun c => (2360344577-1+2*2^9*c.k,98636327818452+c.lower,98636707359301+c.upper)) = pointBounds17978 := by
 decide +kernel
def cuts17979 : List PrefixCut := [⟨19,108035514,108035580⟩,
⟨92,520136244,520136561⟩,
⟨128,720696769,720697213⟩]
theorem checked17979 : checkPrefixCuts (2^48) 2360475649 9 Manual.Count131072.C017979.packed 128 cuts17979 = true := by
 decide +kernel
def pointBounds17979 : List (Nat × Nat × Nat) := [(2360495104,98637157067607,98637536608957),(2360569856,98637569168337,98637948709938)]
theorem point_links_checked17979 : (cuts17979.take 2).map (fun c => (2360475649-1+2*2^9*c.k,98637049032093+c.lower,98637428573377+c.upper)) = pointBounds17979 := by
 decide +kernel
def cuts17980 : List PrefixCut := [⟨37,205684538,205684665⟩,
⟨110,615493741,615494115⟩,
⟨128,717437293,717437726⟩]
theorem checked17980 : checkPrefixCuts (2^48) 2360606721 9 Manual.Count131072.C017980.packed 128 cuts17980 = true := by
 decide +kernel
def pointBounds17980 : List (Nat × Nat × Nat) := [(2360644608,98637975413400,98638354955255),(2360719360,98638385222603,98638764764705)]
theorem point_links_checked17980 : (cuts17980.take 2).map (fun c => (2360606721-1+2*2^9*c.k,98637769728862+c.lower,98638149270590+c.upper)) = pointBounds17980 := by
 decide +kernel
def cuts17981 : List PrefixCut := [⟨55,310714207,310714400⟩,
⟨128,716920697,716921136⟩]
theorem checked17981 : checkPrefixCuts (2^48) 2360737793 9 Manual.Count131072.C017981.packed 128 cuts17981 = true := by
 decide +kernel
def pointBounds17981 : List (Nat × Nat × Nat) := [(2360794112,98638797880362,98639177422716),(2360868864,98639204086852,98639583629452)]
theorem point_links_checked17981 : (cuts17981.take 2).map (fun c => (2360737793-1+2*2^9*c.k,98638487166155+c.lower,98638866708316+c.upper)) = pointBounds17981 := by
 decide +kernel
def cuts17982 : List PrefixCut := [⟨73,406908998,406909247⟩,
⟨128,719384468,719384906⟩]
theorem checked17982 : checkPrefixCuts (2^48) 2360868865 9 Manual.Count131072.C017982.packed 128 cuts17982 = true := by
 decide +kernel
def pointBounds17982 : List (Nat × Nat × Nat) := [(2360943616,98639610995850,98639990538699)]
theorem point_links_checked17982 : (cuts17982.take 1).map (fun c => (2360868865-1+2*2^9*c.k,98639204086852+c.lower,98639583629452+c.upper)) = pointBounds17982 := by
 decide +kernel
def cuts17983 : List PrefixCut := [⟨18,100500813,100500873⟩,
⟨91,518590262,518590581⟩,
⟨128,725066912,725067359⟩]
theorem checked17983 : checkPrefixCuts (2^48) 2360999937 9 Manual.Count131072.C017983.packed 128 cuts17983 = true := by
 decide +kernel
def pointBounds17983 : List (Nat × Nat × Nat) := [(2361018368,98640023972133,98640403515231),(2361093120,98640442061582,98640821604939)]
theorem point_links_checked17983 : (cuts17983.take 2).map (fun c => (2360999937-1+2*2^9*c.k,98639923471320+c.lower,98640303014358+c.upper)) = pointBounds17983 := by
 decide +kernel
def cuts17984 : List PrefixCut := [⟨36,203373900,203374025⟩,
⟨109,617145357,617145739⟩,
⟨128,721688818,721689267⟩]
theorem checked17984 : checkPrefixCuts (2^48) 2361131009 9 Manual.Count131072.C017984.packed 128 cuts17984 = true := by
 decide +kernel
def pointBounds17984 : List (Nat × Nat × Nat) := [(2361167872,98640851912132,98641231455742),(2361242624,98641265683589,98641645227456)]
theorem point_links_checked17984 : (cuts17984.take 2).map (fun c => (2361131009-1+2*2^9*c.k,98640648538232+c.lower,98641028081717+c.upper)) = pointBounds17984 := by
 decide +kernel
def cuts17985 : List PrefixCut := [⟨54,303016304,303016494⟩,
⟨127,722244834,722245281⟩,
⟨128,727847172,727847622⟩]
theorem checked17985 : checkPrefixCuts (2^48) 2361262081 9 Manual.Count131072.C017985.packed 128 cuts17985 = true := by
 decide +kernel
def pointBounds17985 : List (Nat × Nat × Nat) := [(2361317376,98641673243354,98642052787478),(2361392128,98642092471884,98642472016265)]
theorem point_links_checked17985 : (cuts17985.take 2).map (fun c => (2361262081-1+2*2^9*c.k,98641370227050+c.lower,98641749770984+c.upper)) = pointBounds17985 := by
 decide +kernel
def cuts17986 : List PrefixCut := [⟨72,403838703,403838951⟩,
⟨128,725899540,725899979⟩]
theorem checked17986 : checkPrefixCuts (2^48) 2361393153 9 Manual.Count131072.C017986.packed 128 cuts17986 = true := by
 decide +kernel
def pointBounds17986 : List (Nat × Nat × Nat) := [(2361466880,98642501912925,98642881457557)]
theorem point_links_checked17986 : (cuts17986.take 1).map (fun c => (2361393153-1+2*2^9*c.k,98642098074222+c.lower,98642477618606+c.upper)) = pointBounds17986 := by
 decide +kernel
def cuts17987 : List PrefixCut := [⟨17,92969444,92969500⟩,
⟨90,506556307,506556615⟩,
⟨128,717039492,717039923⟩]
theorem checked17987 : checkPrefixCuts (2^48) 2361524225 9 Manual.Count131072.C017987.packed 128 cuts17987 = true := by
 decide +kernel
def pointBounds17987 : List (Nat × Nat × Nat) := [(2361541632,98642916943206,98643296488085),(2361616384,98643330530069,98643710075200)]
theorem point_links_checked17987 : (cuts17987.take 2).map (fun c => (2361524225-1+2*2^9*c.k,98642823973762+c.lower,98643203518585+c.upper)) = pointBounds17987 := by
 decide +kernel
def cuts17988 : List PrefixCut := [⟨35,195700983,195701105⟩,
⟨108,612002824,612003200⟩,
⟨128,727964314,727964759⟩]
theorem checked17988 : checkPrefixCuts (2^48) 2361655297 9 Manual.Count131072.C017988.packed 128 cuts17988 = true := by
 decide +kernel
def pointBounds17988 : List (Nat × Nat × Nat) := [(2361691136,98643736714237,98644116259613),(2361765888,98644153016078,98644532561708)]
theorem point_links_checked17988 : (cuts17988.take 2).map (fun c => (2361655297-1+2*2^9*c.k,98643541013254+c.lower,98643920558508+c.upper)) = pointBounds17988 := by
 decide +kernel
def cuts17989 : List PrefixCut := [⟨53,305809341,305809523⟩,
⟨126,714219252,714219674⟩,
⟨128,724348893,724349322⟩]
theorem checked17989 : checkPrefixCuts (2^48) 2361786369 9 Manual.Count131072.C017989.packed 128 cuts17989 = true := by
 decide +kernel
def pointBounds17989 : List (Nat × Nat × Nat) := [(2361840640,98644574786909,98644954332790),(2361915392,98644983196820,98645362742941)]
theorem point_links_checked17989 : (cuts17989.take 2).map (fun c => (2361786369-1+2*2^9*c.k,98644268977568+c.lower,98644648523267+c.upper)) = pointBounds17989 := by
 decide +kernel
def cuts17990 : List PrefixCut := [⟨71,395645582,395645820⟩,
⟨128,717754107,717754541⟩]
theorem checked17990 : checkPrefixCuts (2^48) 2361917441 9 Manual.Count131072.C017990.packed 128 cuts17990 = true := by
 decide +kernel
def pointBounds17990 : List (Nat × Nat × Nat) := [(2361990144,98645388972043,98645768518409)]
theorem point_links_checked17990 : (cuts17990.take 1).map (fun c => (2361917441-1+2*2^9*c.k,98644993326461+c.lower,98645372872589+c.upper)) = pointBounds17990 := by
 decide +kernel
def cuts17991 : List PrefixCut := [⟨16,90684694,90684747⟩,
⟨89,505371520,505371823⟩,
⟨128,726294101,726294536⟩]
theorem checked17991 : checkPrefixCuts (2^48) 2362048513 9 Manual.Count131072.C017991.packed 128 cuts17991 = true := by
 decide +kernel
def pointBounds17991 : List (Nat × Nat × Nat) := [(2362064896,98645801765262,98646181311877),(2362139648,98646216452088,98646595998953)]
theorem point_links_checked17991 : (cuts17991.take 2).map (fun c => (2362048513-1+2*2^9*c.k,98645711080568+c.lower,98646090627130+c.upper)) = pointBounds17991 := by
 decide +kernel
def cuts17992 : List PrefixCut := [⟨34,191248719,191248836⟩,
⟨107,600785689,600786056⟩,
⟨128,719581159,719581596⟩]
theorem checked17992 : checkPrefixCuts (2^48) 2362179585 9 Manual.Count131072.C017992.packed 128 cuts17992 = true := by
 decide +kernel
def pointBounds17992 : List (Nat × Nat × Nat) := [(2362214400,98646628623388,98647008170502),(2362289152,98647038160358,98647417707722)]
theorem point_links_checked17992 : (cuts17992.take 2).map (fun c => (2362179585-1+2*2^9*c.k,98646437374669+c.lower,98646816921666+c.upper)) = pointBounds17992 := by
 decide +kernel
def cuts17993 : List PrefixCut := [⟨52,297400926,297401108⟩,
⟨125,715371294,715371734⟩,
⟨128,733004876,733005327⟩]
theorem checked17993 : checkPrefixCuts (2^48) 2362310657 9 Manual.Count131072.C017993.packed 128 cuts17993 = true := by
 decide +kernel
def pointBounds17993 : List (Nat × Nat × Nat) := [(2362363904,98647454356754,98647833904370),(2362438656,98647872327122,98648251874996)]
theorem point_links_checked17993 : (cuts17993.take 2).map (fun c => (2362310657-1+2*2^9*c.k,98647156955828+c.lower,98647536503262+c.upper)) = pointBounds17993 := by
 decide +kernel
def cuts17994 : List PrefixCut := [⟨70,393770714,393770953⟩,
⟨128,725815716,725816154⟩]
theorem checked17994 : checkPrefixCuts (2^48) 2362441729 9 Manual.Count131072.C017994.packed 128 cuts17994 = true := by
 decide +kernel
def pointBounds17994 : List (Nat × Nat × Nat) := [(2362513408,98648283731418,98648663279542)]
theorem point_links_checked17994 : (cuts17994.take 1).map (fun c => (2362441729-1+2*2^9*c.k,98647889960704+c.lower,98648269508589+c.upper)) = pointBounds17994 := by
 decide +kernel
def cuts17995 : List PrefixCut := [⟨15,87090428,87090481⟩,
⟨88,496562529,496562827⟩,
⟨128,723631114,723631551⟩]
theorem checked17995 : checkPrefixCuts (2^48) 2362572801 9 Manual.Count131072.C017995.packed 128 cuts17995 = true := by
 decide +kernel
def pointBounds17995 : List (Nat × Nat × Nat) := [(2362588160,98648702866848,98649082415224),(2362662912,98649112338949,98649491887570)]
theorem point_links_checked17995 : (cuts17995.take 2).map (fun c => (2362572801-1+2*2^9*c.k,98648615776420+c.lower,98648995324743+c.upper)) = pointBounds17995 := by
 decide +kernel
def cuts17996 : List PrefixCut := [⟨33,190372442,190372555⟩,
⟨106,604226409,604226771⟩,
⟨128,731096114,731096552⟩]
theorem checked17996 : checkPrefixCuts (2^48) 2362703873 9 Manual.Count131072.C017996.packed 128 cuts17996 = true := by
 decide +kernel
def pointBounds17996 : List (Nat × Nat × Nat) := [(2362737664,98649529779976,98649909328849),(2362812416,98649943633943,98650323183065)]
theorem point_links_checked17996 : (cuts17996.take 2).map (fun c => (2362703873-1+2*2^9*c.k,98649339407534+c.lower,98649718956294+c.upper)) = pointBounds17996 := by
 decide +kernel
def cuts17997 : List PrefixCut := [⟨51,287090328,287090501⟩,
⟨124,697820957,697821381⟩,
⟨128,718666856,718667293⟩]
theorem checked17997 : checkPrefixCuts (2^48) 2362834945 9 Manual.Count131072.C017997.packed 128 cuts17997 = true := by
 decide +kernel
def pointBounds17997 : List (Nat × Nat × Nat) := [(2362887168,98650357593976,98650737143347),(2362961920,98650768324605,98651147874227)]
theorem point_links_checked17997 : (cuts17997.take 2).map (fun c => (2362834945-1+2*2^9*c.k,98650070503648+c.lower,98650450052846+c.upper)) = pointBounds17997 := by
 decide +kernel
def cuts17998 : List PrefixCut := [⟨69,394159885,394160127⟩,
⟨128,721962268,721962711⟩]
theorem checked17998 : checkPrefixCuts (2^48) 2362966017 9 Manual.Count131072.C017998.packed 128 cuts17998 = true := by
 decide +kernel
def pointBounds17998 : List (Nat × Nat × Nat) := [(2363036672,98651183330389,98651562880266)]
theorem point_links_checked17998 : (cuts17998.take 1).map (fun c => (2362966017-1+2*2^9*c.k,98650789170504+c.lower,98651168720139+c.upper)) = pointBounds17998 := by
 decide +kernel
def cuts17999 : List PrefixCut := [⟨14,80877284,80877333⟩,
⟨87,492402666,492402959⟩,
⟨128,721088400,721088834⟩]
theorem checked17999 : checkPrefixCuts (2^48) 2363097089 9 Manual.Count131072.C017999.packed 128 cuts17999 = true := by
 decide +kernel
def pointBounds17999 : List (Nat × Nat × Nat) := [(2363111424,98651592010056,98651971560183),(2363186176,98652003535438,98652383085809)]
theorem point_links_checked17999 : (cuts17999.take 2).map (fun c => (2363097089-1+2*2^9*c.k,98651511132772+c.lower,98651890682850+c.upper)) = pointBounds17999 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000249
