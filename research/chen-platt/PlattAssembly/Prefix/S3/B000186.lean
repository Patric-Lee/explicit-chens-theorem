import PlattAssemblyKernel
import PlattCertificates.Count131072.C025952
import PlattCertificates.Count131072.C025953
import PlattCertificates.Count131072.C025954
import PlattCertificates.Count131072.C025955
import PlattCertificates.Count131072.C025956
import PlattCertificates.Count131072.C025957
import PlattCertificates.Count131072.C025958
import PlattCertificates.Count131072.C025959
import PlattCertificates.Count131072.C025960
import PlattCertificates.Count131072.C025961
import PlattCertificates.Count131072.C025962
import PlattCertificates.Count131072.C025963
import PlattCertificates.Count131072.C025964
import PlattCertificates.Count131072.C025965
import PlattCertificates.Count131072.C025966
import PlattCertificates.Count131072.C025967
import PlattCertificates.Count131072.C025968
import PlattCertificates.Count131072.C025969
import PlattCertificates.Count131072.C025970
import PlattCertificates.Count131072.C025971
import PlattCertificates.Count131072.C025972
import PlattCertificates.Count131072.C025973
import PlattCertificates.Count131072.C025974
import PlattCertificates.Count131072.C025975
import PlattCertificates.Count131072.C025976
import PlattCertificates.Count131072.C025977
import PlattCertificates.Count131072.C025978
import PlattCertificates.Count131072.C025979
import PlattCertificates.Count131072.C025980
import PlattCertificates.Count131072.C025981
import PlattCertificates.Count131072.C025982
import PlattCertificates.Count131072.C025983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000186
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25952 : List PrefixCut := [⟨86,333251478,333251666⟩,
⟨128,499212796,499213078⟩]
theorem checked25952 : checkPrefixCuts (2^48) 3405512705 9 Manual.Count131072.C025952.packed 128 cuts25952 = true := by
 decide +kernel
def pointBounds25952 : List (Nat × Nat × Nat) := [(3405600768,103377431142978,103377813428049)]
theorem point_links_checked25952 : (cuts25952.take 1).map (fun c => (3405512705-1+2*2^9*c.k,103377097891500+c.lower,103377480176383+c.upper)) = pointBounds25952 := by
 decide +kernel
def cuts25953 : List PrefixCut := [⟨62,239846747,239846878⟩,
⟨128,490680947,490681216⟩]
theorem checked25953 : checkPrefixCuts (2^48) 3405643777 9 Manual.Count131072.C025953.packed 128 cuts25953 = true := by
 decide +kernel
def pointBounds25953 : List (Nat × Nat × Nat) := [(3405707264,103377836951043,103378219236339)]
theorem point_links_checked25953 : (cuts25953.take 1).map (fun c => (3405643777-1+2*2^9*c.k,103377597104296+c.lower,103377979389461+c.upper)) = pointBounds25953 := by
 decide +kernel
def cuts25954 : List PrefixCut := [⟨38,149919640,149919726⟩,
⟨128,492149663,492149945⟩]
theorem checked25954 : checkPrefixCuts (2^48) 3405774849 9 Manual.Count131072.C025954.packed 128 cuts25954 = true := by
 decide +kernel
def pointBounds25954 : List (Nat × Nat × Nat) := [(3405813760,103378237704883,103378619990403)]
theorem point_links_checked25954 : (cuts25954.take 1).map (fun c => (3405774849-1+2*2^9*c.k,103378087785243+c.lower,103378470070677+c.upper)) = pointBounds25954 := by
 decide +kernel
def cuts25955 : List PrefixCut := [⟨14,50660165,50660191⟩,
⟨118,449653540,449653796⟩,
⟨128,487915915,487916195⟩]
theorem checked25955 : checkPrefixCuts (2^48) 3405905921 9 Manual.Count131072.C025955.packed 128 cuts25955 = true := by
 decide +kernel
def pointBounds25955 : List (Nat × Nat × Nat) := [(3405920256,103378630595071,103379012880813),(3406026752,103379029588446,103379411874418)]
theorem point_links_checked25955 : (cuts25955.take 2).map (fun c => (3405905921-1+2*2^9*c.k,103378579934906+c.lower,103378962220622+c.upper)) = pointBounds25955 := by
 decide +kernel
def cuts25956 : List PrefixCut := [⟨94,361462240,361462440⟩,
⟨128,494590838,494591112⟩]
theorem checked25956 : checkPrefixCuts (2^48) 3406036993 9 Manual.Count131072.C025956.packed 128 cuts25956 = true := by
 decide +kernel
def pointBounds25956 : List (Nat × Nat × Nat) := [(3406133248,103379429313061,103379811599257)]
theorem point_links_checked25956 : (cuts25956.take 1).map (fun c => (3406036993-1+2*2^9*c.k,103379067850821+c.lower,103379450136817+c.upper)) = pointBounds25956 := by
 decide +kernel
def cuts25957 : List PrefixCut := [⟨70,266500922,266501073⟩,
⟨128,490357425,490357698⟩]
theorem checked25957 : checkPrefixCuts (2^48) 3406168065 9 Manual.Count131072.C025957.packed 128 cuts25957 = true := by
 decide +kernel
def pointBounds25957 : List (Nat × Nat × Nat) := [(3406239744,103379828942581,103380211229002)]
theorem point_links_checked25957 : (cuts25957.take 1).map (fun c => (3406168065-1+2*2^9*c.k,103379562441659+c.lower,103379944727929+c.upper)) = pointBounds25957 := by
 decide +kernel
def cuts25958 : List PrefixCut := [⟨46,172785742,172785841⟩,
⟨128,494718000,494718278⟩]
theorem checked25958 : checkPrefixCuts (2^48) 3406299137 9 Manual.Count131072.C025958.packed 128 cuts25958 = true := by
 decide +kernel
def pointBounds25958 : List (Nat × Nat × Nat) := [(3406346240,103380225584826,103380607871468)]
theorem point_links_checked25958 : (cuts25958.take 1).map (fun c => (3406299137-1+2*2^9*c.k,103380052799084+c.lower,103380435085627+c.upper)) = pointBounds25958 := by
 decide +kernel
def cuts25959 : List PrefixCut := [⟨22,85604877,85604926⟩,
⟨126,481065462,481065732⟩,
⟨128,488915056,488915330⟩]
theorem checked25959 : checkPrefixCuts (2^48) 3406430209 9 Manual.Count131072.C025959.packed 128 cuts25959 = true := by
 decide +kernel
def pointBounds25959 : List (Nat × Nat × Nat) := [(3406452736,103380633121961,103381015408831),(3406559232,103381028582546,103381410869637)]
theorem point_links_checked25959 : (cuts25959.take 2).map (fun c => (3406430209-1+2*2^9*c.k,103380547517084+c.lower,103380929803905+c.upper)) = pointBounds25959 := by
 decide +kernel
def cuts25960 : List PrefixCut := [⟨102,394291369,394291589⟩,
⟨128,494349549,494349825⟩]
theorem checked25960 : checkPrefixCuts (2^48) 3406561281 9 Manual.Count131072.C025960.packed 128 cuts25960 = true := by
 decide +kernel
def pointBounds25960 : List (Nat × Nat × Nat) := [(3406665728,103381430723509,103381813010824)]
theorem point_links_checked25960 : (cuts25960.take 1).map (fun c => (3406561281-1+2*2^9*c.k,103381036432140+c.lower,103381418719235+c.upper)) = pointBounds25960 := by
 decide +kernel
def cuts25961 : List PrefixCut := [⟨78,298434787,298434951⟩,
⟨128,490282011,490282280⟩]
theorem checked25961 : checkPrefixCuts (2^48) 3406692353 9 Manual.Count131072.C025961.packed 128 cuts25961 = true := by
 decide +kernel
def pointBounds25961 : List (Nat × Nat × Nat) := [(3406772224,103381829216476,103382211504011)]
theorem point_links_checked25961 : (cuts25961.take 1).map (fun c => (3406692353-1+2*2^9*c.k,103381530781689+c.lower,103381913069060+c.upper)) = pointBounds25961 := by
 decide +kernel
def cuts25962 : List PrefixCut := [⟨54,210185914,210186029⟩,
⟨128,492741729,492741997⟩]
theorem checked25962 : checkPrefixCuts (2^48) 3406823425 9 Manual.Count131072.C025962.packed 128 cuts25962 = true := by
 decide +kernel
def pointBounds25962 : List (Nat × Nat × Nat) := [(3406878720,103382231249614,103382613537369)]
theorem point_links_checked25962 : (cuts25962.take 1).map (fun c => (3406823425-1+2*2^9*c.k,103382021063700+c.lower,103382403351340+c.upper)) = pointBounds25962 := by
 decide +kernel
def cuts25963 : List PrefixCut := [⟨30,115168620,115168687⟩,
⟨128,490079011,490079286⟩]
theorem checked25963 : checkPrefixCuts (2^48) 3406954497 9 Manual.Count131072.C025963.packed 128 cuts25963 = true := by
 decide +kernel
def pointBounds25963 : List (Nat × Nat × Nat) := [(3406985216,103382628974049,103383011262024)]
theorem point_links_checked25963 : (cuts25963.take 1).map (fun c => (3406954497-1+2*2^9*c.k,103382513805429+c.lower,103382896093337+c.upper)) = pointBounds25963 := by
 decide +kernel
def cuts25964 : List PrefixCut := [⟨6,24288661,24288673⟩,
⟨110,426366719,426366956⟩,
⟨128,495264805,495265080⟩]
theorem checked25964 : checkPrefixCuts (2^48) 3407085569 9 Manual.Count131072.C025964.packed 128 cuts25964 = true := by
 decide +kernel
def pointBounds25964 : List (Nat × Nat × Nat) := [(3407091712,103383028173101,103383410461296),(3407198208,103383430251159,103383812539579)]
theorem point_links_checked25964 : (cuts25964.take 2).map (fun c => (3407085569-1+2*2^9*c.k,103383003884440+c.lower,103383386172623+c.upper)) = pointBounds25964 := by
 decide +kernel
def cuts25965 : List PrefixCut := [⟨86,331267363,331267546⟩,
⟨128,494584833,494585108⟩]
theorem checked25965 : checkPrefixCuts (2^48) 3407216641 9 Manual.Count131072.C025965.packed 128 cuts25965 = true := by
 decide +kernel
def pointBounds25965 : List (Nat × Nat × Nat) := [(3407304704,103383830416608,103384212705249)]
theorem point_links_checked25965 : (cuts25965.take 1).map (fun c => (3407216641-1+2*2^9*c.k,103383499149245+c.lower,103383881437703+c.upper)) = pointBounds25965 := by
 decide +kernel
def cuts25966 : List PrefixCut := [⟨62,240222439,240222573⟩,
⟨128,495722362,495722639⟩]
theorem checked25966 : checkPrefixCuts (2^48) 3407347713 9 Manual.Count131072.C025966.packed 128 cuts25966 = true := by
 decide +kernel
def pointBounds25966 : List (Nat × Nat × Nat) := [(3407411200,103384233956517,103384616245384)]
theorem point_links_checked25966 : (cuts25966.take 1).map (fun c => (3407347713-1+2*2^9*c.k,103383993734078+c.lower,103384376022811+c.upper)) = pointBounds25966 := by
 decide +kernel
def cuts25967 : List PrefixCut := [⟨38,148605612,148605697⟩,
⟨128,495868514,495868795⟩]
theorem checked25967 : checkPrefixCuts (2^48) 3407478785 9 Manual.Count131072.C025967.packed 128 cuts25967 = true := by
 decide +kernel
def pointBounds25967 : List (Nat × Nat × Nat) := [(3407517696,103384638062052,103385020351147)]
theorem point_links_checked25967 : (cuts25967.take 1).map (fun c => (3407478785-1+2*2^9*c.k,103384489456440+c.lower,103384871745450+c.upper)) = pointBounds25967 := by
 decide +kernel
def cuts25968 : List PrefixCut := [⟨14,54186704,54186735⟩,
⟨118,450502482,450502741⟩,
⟨128,488910927,488911208⟩]
theorem checked25968 : checkPrefixCuts (2^48) 3407609857 9 Manual.Count131072.C025968.packed 128 cuts25968 = true := by
 decide +kernel
def pointBounds25968 : List (Nat × Nat × Nat) := [(3407624192,103385039511658,103385421800980),(3407730688,103385435827436,103385818116986)]
theorem point_links_checked25968 : (cuts25968.take 2).map (fun c => (3407609857-1+2*2^9*c.k,103384985324954+c.lower,103385367614245+c.upper)) = pointBounds25968 := by
 decide +kernel
def cuts25969 : List PrefixCut := [⟨94,362190135,362190339⟩,
⟨128,497317065,497317344⟩]
theorem checked25969 : checkPrefixCuts (2^48) 3407740929 9 Manual.Count131072.C025969.packed 128 cuts25969 = true := by
 decide +kernel
def pointBounds25969 : List (Nat × Nat × Nat) := [(3407837184,103385836426016,103386218715792)]
theorem point_links_checked25969 : (cuts25969.take 1).map (fun c => (3407740929-1+2*2^9*c.k,103385474235881+c.lower,103385856525453+c.upper)) = pointBounds25969 := by
 decide +kernel
def cuts25970 : List PrefixCut := [⟨70,269671483,269671633⟩,
⟨128,491929360,491929632⟩]
theorem checked25970 : checkPrefixCuts (2^48) 3407872001 9 Manual.Count131072.C025970.packed 128 cuts25970 = true := by
 decide +kernel
def pointBounds25970 : List (Nat × Nat × Nat) := [(3407943680,103386241224429,103386623514430)]
theorem point_links_checked25970 : (cuts25970.take 1).map (fun c => (3407872001-1+2*2^9*c.k,103385971552946+c.lower,103386353842797+c.upper)) = pointBounds25970 := by
 decide +kernel
def cuts25971 : List PrefixCut := [⟨47,181536673,181536774⟩,
⟨128,495544448,495544728⟩]
theorem checked25971 : checkPrefixCuts (2^48) 3408003073 9 Manual.Count131072.C025971.packed 128 cuts25971 = true := by
 decide +kernel
def pointBounds25971 : List (Nat × Nat × Nat) := [(3408051200,103386645018979,103387027309203)]
theorem point_links_checked25971 : (cuts25971.take 1).map (fun c => (3408003073-1+2*2^9*c.k,103386463482306+c.lower,103386845772429+c.upper)) = pointBounds25971 := by
 decide +kernel
def cuts25972 : List PrefixCut := [⟨24,91425847,91425899⟩,
⟨128,495525326,495525611⟩]
theorem checked25972 : checkPrefixCuts (2^48) 3408134145 9 Manual.Count131072.C025972.packed 128 cuts25972 = true := by
 decide +kernel
def pointBounds25972 : List (Nat × Nat × Nat) := [(3408158720,103387050452601,103387432743056)]
theorem point_links_checked25972 : (cuts25972.take 1).map (fun c => (3408134145-1+2*2^9*c.k,103386959026754+c.lower,103387341317157+c.upper)) = pointBounds25972 := by
 decide +kernel
def cuts25973 : List PrefixCut := [⟨1,3716368,3716370⟩,
⟨106,408546320,408546549⟩,
⟨128,488982229,488982506⟩]
theorem checked25973 : checkPrefixCuts (2^48) 3408265217 9 Manual.Count131072.C025973.packed 128 cuts25973 = true := by
 decide +kernel
def pointBounds25973 : List (Nat × Nat × Nat) := [(3408266240,103387458268448,103387840559138),(3408373760,103387863098400,103388245389317)]
theorem point_links_checked25973 : (cuts25973.take 2).map (fun c => (3408265217-1+2*2^9*c.k,103387454552080+c.lower,103387836842768+c.upper)) = pointBounds25973 := by
 decide +kernel
def cuts25974 : List PrefixCut := [⟨83,322646959,322647133⟩,
⟨128,492927289,492927559⟩]
theorem checked25974 : checkPrefixCuts (2^48) 3408396289 9 Manual.Count131072.C025974.packed 128 cuts25974 = true := by
 decide +kernel
def pointBounds25974 : List (Nat × Nat × Nat) := [(3408481280,103388266181268,103388648472407)]
theorem point_links_checked25974 : (cuts25974.take 1).map (fun c => (3408396289-1+2*2^9*c.k,103387943534309+c.lower,103388325825274+c.upper)) = pointBounds25974 := by
 decide +kernel
def cuts25975 : List PrefixCut := [⟨60,229651841,229651969⟩,
⟨128,495137793,495138070⟩]
theorem checked25975 : checkPrefixCuts (2^48) 3408527361 9 Manual.Count131072.C025975.packed 128 cuts25975 = true := by
 decide +kernel
def pointBounds25975 : List (Nat × Nat × Nat) := [(3408588800,103388666113439,103389048404802)]
theorem point_links_checked25975 : (cuts25975.take 1).map (fun c => (3408527361-1+2*2^9*c.k,103388436461598+c.lower,103388818752833+c.upper)) = pointBounds25975 := by
 decide +kernel
def cuts25976 : List PrefixCut := [⟨37,141700398,141700481⟩,
⟨128,489090853,489091125⟩]
theorem checked25976 : checkPrefixCuts (2^48) 3408658433 9 Manual.Count131072.C025976.packed 128 cuts25976 = true := by
 decide +kernel
def pointBounds25976 : List (Nat × Nat × Nat) := [(3408696320,103389073299789,103389455591384)]
theorem point_links_checked25976 : (cuts25976.take 1).map (fun c => (3408658433-1+2*2^9*c.k,103388931599391+c.lower,103389313890903+c.upper)) = pointBounds25976 := by
 decide +kernel
def cuts25977 : List PrefixCut := [⟨14,55158828,55158858⟩,
⟨119,462567207,462567466⟩,
⟨128,497081555,497081834⟩]
theorem checked25977 : checkPrefixCuts (2^48) 3408789505 9 Manual.Count131072.C025977.packed 128 cuts25977 = true := by
 decide +kernel
def pointBounds25977 : List (Nat × Nat × Nat) := [(3408803840,103389475849072,103389858140886),(3408911360,103389883257451,103390265549494)]
theorem point_links_checked25977 : (cuts25977.take 2).map (fun c => (3408789505-1+2*2^9*c.k,103389420690244+c.lower,103389802982028+c.upper)) = pointBounds25977 := by
 decide +kernel
def cuts25978 : List PrefixCut := [⟨96,371477467,371477677⟩,
⟨128,497310065,497310344⟩]
theorem checked25978 : checkPrefixCuts (2^48) 3408920577 9 Manual.Count131072.C025978.packed 128 cuts25978 = true := by
 decide +kernel
def pointBounds25978 : List (Nat × Nat × Nat) := [(3409018880,103390289249266,103390671541539)]
theorem point_links_checked25978 : (cuts25978.take 1).map (fun c => (3408920577-1+2*2^9*c.k,103389917771799+c.lower,103390300063862+c.upper)) = pointBounds25978 := by
 decide +kernel
def cuts25979 : List PrefixCut := [⟨73,283779417,283779572⟩,
⟨128,495309498,495309769⟩]
theorem checked25979 : checkPrefixCuts (2^48) 3409051649 9 Manual.Count131072.C025979.packed 128 cuts25979 = true := by
 decide +kernel
def pointBounds25979 : List (Nat × Nat × Nat) := [(3409126400,103390698861281,103391081153778)]
theorem point_links_checked25979 : (cuts25979.take 1).map (fun c => (3409051649-1+2*2^9*c.k,103390415081864+c.lower,103390797374206+c.upper)) = pointBounds25979 := by
 decide +kernel
def cuts25980 : List PrefixCut := [⟨50,191959257,191959364⟩,
⟨128,492152980,492153261⟩]
theorem checked25980 : checkPrefixCuts (2^48) 3409182721 9 Manual.Count131072.C025980.packed 128 cuts25980 = true := by
 decide +kernel
def pointBounds25980 : List (Nat × Nat × Nat) := [(3409233920,103391102350619,103391484643339)]
theorem point_links_checked25980 : (cuts25980.take 1).map (fun c => (3409182721-1+2*2^9*c.k,103390910391362+c.lower,103391292683975+c.upper)) = pointBounds25980 := by
 decide +kernel
def cuts25981 : List PrefixCut := [⟨27,108814401,108814461⟩,
⟨128,489079575,489079846⟩]
theorem checked25981 : checkPrefixCuts (2^48) 3409313793 9 Manual.Count131072.C025981.packed 128 cuts25981 = true := by
 decide +kernel
def pointBounds25981 : List (Nat × Nat × Nat) := [(3409341440,103391511358743,103391893651697)]
theorem point_links_checked25981 : (cuts25981.take 1).map (fun c => (3409313793-1+2*2^9*c.k,103391402544342+c.lower,103391784837236+c.upper)) = pointBounds25981 := by
 decide +kernel
def cuts25982 : List PrefixCut := [⟨4,14282422,14282430⟩,
⟨109,419549824,419550056⟩,
⟨128,490711770,490712040⟩]
theorem checked25982 : checkPrefixCuts (2^48) 3409444865 9 Manual.Count131072.C025982.packed 128 cuts25982 = true := by
 decide +kernel
def pointBounds25982 : List (Nat × Nat × Nat) := [(3409448960,103391905906339,103392288199512),(3409556480,103392311173741,103392693467138)]
theorem point_links_checked25982 : (cuts25982.take 2).map (fun c => (3409444865-1+2*2^9*c.k,103391891623917+c.lower,103392273917082+c.upper)) = pointBounds25982 := by
 decide +kernel
def cuts25983 : List PrefixCut := [⟨86,328231413,328231595⟩,
⟨128,493582193,493582469⟩]
theorem checked25983 : checkPrefixCuts (2^48) 3409575937 9 Manual.Count131072.C025983.packed 128 cuts25983 = true := by
 decide +kernel
def pointBounds25983 : List (Nat × Nat × Nat) := [(3409664000,103392710567100,103393092860717)]
theorem point_links_checked25983 : (cuts25983.take 1).map (fun c => (3409575937-1+2*2^9*c.k,103392382335687+c.lower,103392764629122+c.upper)) = pointBounds25983 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000186
