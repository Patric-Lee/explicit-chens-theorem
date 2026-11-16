import PlattPointSubsetKernel
import PlattPointPackets.S4B000072
import PlattPointPackets.S4B000073
import PlattPointPackets.S4B000074
import PlattPointPackets.S4B000075
import PlattPointPackets.S4B000076
import PlattPointPackets.S4B000077
import PlattPointPackets.S4B000078
import PlattPointPackets.S4B000079
import PlattPointPackets.S4B000080
import PlattPointPackets.S4B000081
import PlattGlobalGrid.S8B000010
namespace ChenEffective.PlattWindow.PointCovers.S8B000010
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000072.points ++ ChenEffective.PlattWindow.PointPackets.S4B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000081.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000010.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000010.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000010
