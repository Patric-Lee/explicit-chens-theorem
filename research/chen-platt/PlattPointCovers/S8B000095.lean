import PlattPointSubsetKernel
import PlattPointPackets.S7B000127
import PlattPointPackets.S7B000128
import PlattPointPackets.S7B000129
import PlattPointPackets.S7B000130
import PlattPointPackets.S7B000131
import PlattPointPackets.S7B000132
import PlattPointPackets.S7B000133
import PlattPointPackets.S7B000134
import PlattPointPackets.S7B000135
import PlattPointPackets.S7B000136
import PlattPointPackets.S7B000137
import PlattPointPackets.S7B000138
import PlattPointPackets.S7B000139
import PlattPointPackets.S7B000140
import PlattPointPackets.S7B000141
import PlattPointPackets.S7B000142
import PlattPointPackets.S7B000143
import PlattGlobalGrid.S8B000095
namespace ChenEffective.PlattWindow.PointCovers.S8B000095
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000127.points ++ ChenEffective.PlattWindow.PointPackets.S7B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000140.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000141.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000142.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000143.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000095.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000095.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000095
