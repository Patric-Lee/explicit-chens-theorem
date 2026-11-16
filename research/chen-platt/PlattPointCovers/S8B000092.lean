import PlattPointSubsetKernel
import PlattPointPackets.S7B000080
import PlattPointPackets.S7B000081
import PlattPointPackets.S7B000082
import PlattPointPackets.S7B000083
import PlattPointPackets.S7B000084
import PlattPointPackets.S7B000085
import PlattPointPackets.S7B000086
import PlattPointPackets.S7B000087
import PlattPointPackets.S7B000088
import PlattPointPackets.S7B000089
import PlattPointPackets.S7B000090
import PlattPointPackets.S7B000091
import PlattPointPackets.S7B000092
import PlattPointPackets.S7B000093
import PlattPointPackets.S7B000094
import PlattPointPackets.S7B000095
import PlattGlobalGrid.S8B000092
namespace ChenEffective.PlattWindow.PointCovers.S8B000092
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000080.points ++ ChenEffective.PlattWindow.PointPackets.S7B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000082.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000083.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000086.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000087.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000088.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000089.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000090.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000093.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000095.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000092.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000092.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000092
