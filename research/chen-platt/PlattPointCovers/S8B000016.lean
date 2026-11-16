import PlattPointSubsetKernel
import PlattPointPackets.S4B000122
import PlattPointPackets.S4B000123
import PlattPointPackets.S4B000124
import PlattPointPackets.S4B000125
import PlattPointPackets.S4B000126
import PlattPointPackets.S4B000127
import PlattPointPackets.S4B000128
import PlattPointPackets.S4B000129
import PlattPointPackets.S4B000130
import PlattPointPackets.S4B000131
import PlattGlobalGrid.S8B000016
namespace ChenEffective.PlattWindow.PointCovers.S8B000016
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000122.points ++ ChenEffective.PlattWindow.PointPackets.S4B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000131.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000016.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000016.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000016
